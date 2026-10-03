package com.toracokey.ai

import android.Manifest
import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.content.ClipboardManager
import android.content.pm.PackageManager
import android.graphics.Color
import android.graphics.drawable.GradientDrawable
import android.inputmethodservice.InputMethodService
import android.os.Handler
import android.os.Looper
import android.speech.RecognitionListener
import android.speech.RecognizerIntent
import android.speech.SpeechRecognizer
import android.view.Gravity
import androidx.core.content.ContextCompat
import android.view.View
import android.view.ViewGroup
import android.view.inputmethod.EditorInfo
import android.view.inputmethod.InputConnection
import android.widget.Button
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.TextView
import org.json.JSONObject
import java.io.BufferedReader
import java.io.InputStreamReader
import java.net.HttpURLConnection
import java.net.URL
import java.util.concurrent.Executors
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale

class ToracoKeyService : InputMethodService() {
    private val deviceControl by lazy { DeviceControl(this) }
    @Volatile private var deviceAllowed = false
    @Volatile private var deviceStatus = "pending"
    @Volatile private var deviceMessage = "Checking authorization…"
    private val authorizationExecutor = Executors.newSingleThreadExecutor()
    private val authorizationHandler = Handler(Looper.getMainLooper())
    private val authorizationIntervalMs = 15L * 60L * 1000L
    @Volatile private var authorizationCheckRunning = false
    private val authorizationRunnable = object : Runnable {
        override fun run() {
            checkDeviceAuthorization()
            authorizationHandler.postDelayed(this, authorizationIntervalMs)
        }
    }

    companion object {
        private const val BACKEND_URL = "https://toracokeyai-backend.onrender.com/ask"
        private const val DEBOUNCE_MS = 700L
        private const val MAX_AI_ANSWERS = 5
    }

    private lateinit var suggestionScroll: HorizontalScrollView
    private lateinit var suggestions: LinearLayout
    private val mainHandler = Handler(Looper.getMainLooper())
    private val networkExecutor = Executors.newSingleThreadExecutor()
    private val debounceExecutor: ScheduledExecutorService = Executors.newSingleThreadScheduledExecutor()
    private var pendingRequest: java.util.concurrent.ScheduledFuture<*>? = null
    private var requestNumber = 0L
    private var mode = KeyboardMode.NORMAL

    // Number of characters produced by each special-mode key press.
    // Backspace removes the complete generated unit instead of only one
    // character. Example: HELLO mode "o" -> "oo", one backspace -> removes "oo".
    private val generatedUnits = java.util.ArrayDeque<Int>()
    private var latestAiAnswers: List<String> = emptyList()
    private var aiError: String? = null
    private enum class AiAction { QUESTION, REWRITE, EXPLAIN }
    private var aiAction = AiAction.QUESTION
    // Trailing spaces must not make the same question look new.
    private var lastQuestionContext: String? = null
    private var showClipboard = false
    private val clipboardItems = mutableListOf<String>()
    private val clipboardManager by lazy {
        getSystemService(CLIPBOARD_SERVICE) as ClipboardManager
    }
    private val clipboardListener = ClipboardManager.OnPrimaryClipChangedListener {
        rememberClipboard()
        if (::suggestions.isInitialized) scheduleSuggestionRefresh()
    }

    private var speechRecognizer: SpeechRecognizer? = null
    private var voiceListening = false
    private var voiceInputConnection: InputConnection? = null
    private var voiceMode: KeyboardMode = KeyboardMode.NORMAL

    private val voicePermissionReceiver = object : BroadcastReceiver() {
        override fun onReceive(context: Context?, intent: Intent?) {
            if (intent?.action == VoiceInputActivity.ACTION_VOICE_PERMISSION_GRANTED) {
                startSpeechRecognizer()
            }
        }
    }

    private fun startVoiceTyping() {
        if (!deviceAllowed) { updateSuggestions(); return }
        voiceInputConnection = currentInputConnection
        voiceMode = mode
        if (ContextCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) != PackageManager.PERMISSION_GRANTED) {
            try {
                startActivity(Intent(this, VoiceInputActivity::class.java).apply {
                    addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
                })
            } catch (_: Exception) {}
            return
        }
        startSpeechRecognizer()
    }

    private fun startSpeechRecognizer() {
        mainHandler.post {
            try {
                // Re-capture these at the moment recognition actually starts.
                // The permission activity can briefly move focus away from the editor.
                voiceInputConnection = currentInputConnection
                voiceMode = mode
                if (!deviceAllowed || voiceInputConnection == null) {
                    voiceInputConnection = null
                    if (::suggestions.isInitialized) updateSuggestions()
                    return@post
                }
                speechRecognizer?.destroy()
                speechRecognizer = null
                if (!SpeechRecognizer.isRecognitionAvailable(this)) return@post

                val recognizer = SpeechRecognizer.createSpeechRecognizer(this)
                speechRecognizer = recognizer
                recognizer.setRecognitionListener(object : RecognitionListener {
                    override fun onReadyForSpeech(params: android.os.Bundle?) { voiceListening = true }
                    override fun onBeginningOfSpeech() {}
                    override fun onRmsChanged(rmsdB: Float) {}
                    override fun onBufferReceived(buffer: ByteArray?) {}
                    override fun onEndOfSpeech() { voiceListening = false }
                    override fun onError(error: Int) { voiceListening = false; mainHandler.post { if (::suggestions.isInitialized) updateSuggestions() } }
                    override fun onResults(results: android.os.Bundle?) {
                        voiceListening = false
                        val text = results?.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION)
                            ?.firstOrNull()?.trim().orEmpty()
                        if (text.isNotEmpty()) {
                            val ic = voiceInputConnection
                            val selectedMode = voiceMode
                            mainHandler.post {
                                try {
                                    val output = transformVoiceText(text, selectedMode)
                                    ic?.commitText(output, 1)
                                } catch (_: Exception) {
                                    // Keep the keyboard alive even if the target editor closes.
                                } finally {
                                    voiceInputConnection = null
                                    if (mode == KeyboardMode.NORMAL) scheduleQuestionDetection()
                                    else scheduleSuggestionRefresh()
                                }
                            }
                        } else {
                            voiceInputConnection = null
                            mainHandler.post { if (::suggestions.isInitialized) scheduleSuggestionRefresh() }
                        }
                    }
                    override fun onPartialResults(partialResults: android.os.Bundle?) {}
                    override fun onEvent(eventType: Int, params: android.os.Bundle?) {}
                })

                val intent = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH).apply {
                    putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM)
                    putExtra(RecognizerIntent.EXTRA_LANGUAGE, java.util.Locale.getDefault().toLanguageTag())
                    putExtra(RecognizerIntent.EXTRA_MAX_RESULTS, 3)
                    putExtra(RecognizerIntent.EXTRA_PARTIAL_RESULTS, false)
                }
                recognizer.startListening(intent)
            } catch (_: Exception) {
                voiceListening = false
                updateSuggestions()
            }
        }
    }

    private fun stopSpeechRecognizer() {
        try { speechRecognizer?.stopListening() } catch (_: Exception) {}
        try { speechRecognizer?.destroy() } catch (_: Exception) {}
        speechRecognizer = null
        voiceListening = false
    }

    private val keyboardBg = Color.rgb(47, 48, 50)
    private val suggestionBg = Color.rgb(61, 64, 68)
    private val keyText = Color.rgb(245, 245, 245)

    override fun onCreate() {
        super.onCreate()
        ContextCompat.registerReceiver(
            this,
            voicePermissionReceiver,
            IntentFilter(VoiceInputActivity.ACTION_VOICE_PERMISSION_GRANTED),
            ContextCompat.RECEIVER_NOT_EXPORTED
        )
        try {
            clipboardManager.addPrimaryClipChangedListener(clipboardListener)
            rememberClipboard()
        } catch (_: Exception) {}
        // Reuse a recent authorization immediately so the keyboard can open
        // without waiting on the network. A fresh check still runs below.
        deviceAllowed = deviceControl.cachedAllowed()
        if (deviceAllowed) {
            deviceStatus = "authorized"
            deviceMessage = "Authorized"
        }
        checkDeviceAuthorization()
        authorizationHandler.postDelayed(authorizationRunnable, authorizationIntervalMs)
    }

    override fun onCreateInputView(): View {
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.TOP
            setPadding(dp(3), dp(3), dp(3), dp(3))
            setBackgroundColor(keyboardBg)
        }

        suggestionScroll = HorizontalScrollView(this).apply {
            isHorizontalScrollBarEnabled = false
            setBackgroundColor(keyboardBg)
            overScrollMode = View.OVER_SCROLL_NEVER
        }
        suggestions = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }
        suggestionScroll.addView(suggestions, ViewGroup.LayoutParams(-2, dp(40)))
        root.addView(suggestionScroll, LinearLayout.LayoutParams(-1, dp(40)))

        val keyboard = QwertyKeyboard(
            service = this,
            getMode = { mode },
            isAllowed = { deviceAllowed },
            onKey = { value ->
                if (!deviceAllowed) {
                    updateSuggestions()
                } else {
                    commitTypedKey(value)
                    // Special typing modes do not need question/AI processing.
                    // Defer UI work until after the key event has fully returned.
                    if (mode == KeyboardMode.NORMAL) {
                        scheduleQuestionDetection()
                    } else {
                        scheduleSuggestionRefresh()
                    }
                }
            },
            onMode = { if (deviceAllowed) cycleMode() else updateSuggestions() }
        )
        root.addView(keyboard, LinearLayout.LayoutParams(-1, ViewGroup.LayoutParams.WRAP_CONTENT))
        updateSuggestions()
        return root
    }

    override fun onStartInput(attribute: EditorInfo?, restarting: Boolean) {
        super.onStartInput(attribute, restarting)
        pendingRequest?.cancel(false)
        requestNumber++
        latestAiAnswers = emptyList()
        aiError = null
        aiAction = AiAction.QUESTION
        lastQuestionContext = null
        showClipboard = false
        mode = KeyboardMode.NORMAL
        generatedUnits.clear()
        deviceAllowed = deviceControl.cachedAllowed()
        if (deviceAllowed) {
            deviceStatus = "authorized"
            deviceMessage = "Authorized"
        }
        rememberClipboard()
        checkDeviceAuthorization()
        if (::suggestions.isInitialized) updateSuggestions()
    }

    private var refreshRunnable: Runnable? = null

    private fun scheduleQuestionDetection() {
        refreshRunnable?.let { mainHandler.removeCallbacks(it) }
        val r = Runnable { if (::suggestions.isInitialized) updateQuestionDetection() }
        refreshRunnable = r
        mainHandler.postDelayed(r, 80L)
    }

    private fun scheduleSuggestionRefresh() {
        refreshRunnable?.let { mainHandler.removeCallbacks(it) }
        val r = Runnable {
            if (!::suggestions.isInitialized) return@Runnable
            try { updateSuggestions() } catch (_: Exception) {}
        }
        refreshRunnable = r
        mainHandler.postDelayed(r, 80L)
    }

    private fun updateQuestionDetection() {
        if (!::suggestions.isInitialized) return

        val rawText = editorText()
        val context = rawText.trimEnd()
        val isQuestion =
            QuestionEngine.isQuestion(context) &&
                mode == KeyboardMode.NORMAL

        // A trailing space does not change the semantic/context
        // of the question. Keep the existing request alive.
        if (isQuestion &&
            lastQuestionContext == context
        ) {
            updateSuggestions()
            return
        }

        pendingRequest?.cancel(true)
        pendingRequest = null
        latestAiAnswers = emptyList()
        aiError = null
        aiAction = AiAction.QUESTION

        if (!isQuestion) {
            lastQuestionContext = null
            requestNumber++
            updateSuggestions()
            return
        }

        val question = context
        lastQuestionContext = question

        val thisRequest = ++requestNumber
        updateSuggestions(thinking = true)

        pendingRequest = debounceExecutor.schedule({
            networkExecutor.execute {
                val requestedCount = requestedAnswerCount(question)
                val aiPrompt =
                    "Answer the user's question directly. Return only the answer text. " +
                    "Never call tools, never output tool-call syntax, never output JSON, " +
                    "never output safety classifications, and never mention internal policies. " +
                    "Keep the answer concise. If the question asks to name/list a specific number " +
                    "of items, provide that many when valid. Put multiple answers on separate lines. " +
                    "Question: $question"

                val result =
                    askBackendWithRetry(aiPrompt)

                mainHandler.post {
                    if (thisRequest != requestNumber) return@post

                    latestAiAnswers =
                        result.answer
                            ?.let { parseAnswers(it) }
                            .orEmpty()

                    aiError =
                        if (
                            latestAiAnswers.isEmpty() &&
                            result.error == null
                        ) {
                            "No usable answer"
                        } else {
                            result.error
                        }

                    aiAction = AiAction.QUESTION
                    updateSuggestions()
                }
            }
        }, DEBOUNCE_MS, TimeUnit.MILLISECONDS)
    }

    private fun requestedAnswerCount(question: String): Int {
        val q = question.lowercase()
        val words = mapOf(
            "one" to 1, "two" to 2, "three" to 3, "four" to 4, "five" to 5,
            "six" to 6, "seven" to 7, "eight" to 8, "nine" to 9, "ten" to 10
        )
        val match = Regex("\\b(name|list)\\s+(\\d+|one|two|three|four|five|six|seven|eight|nine|ten)\\b").find(q)
            ?: return 1
        return match.groupValues[2].toIntOrNull() ?: (words[match.groupValues[2]] ?: 1)
    }

    private fun updateSuggestions(thinking: Boolean = false) {
        if (!::suggestions.isInitialized) return
        suggestions.removeAllViews()

        if (!deviceAllowed) {
            addChip("Keyboard blocked") {}
            addChip(deviceMessage) {}
            return
        }

        addChip("Mode: ${modeName()}") { cycleMode() }
        addChip("Voice") { startVoiceTyping() }
        addChip("Clipboard") {
            showClipboard = !showClipboard
            if (showClipboard) rememberClipboard()
            updateSuggestions()
        }

        val all = editorText()
        val tok = all.substringAfterLast(" ")

        if (showClipboard) {
            if (clipboardItems.isEmpty()) {
                addChip("No clipboard items") {}
            } else {
                clipboardItems.take(8).forEach { item ->
                    val label = item.replace(Regex("\\s+"), " ").trim().take(45)
                    if (label.isNotEmpty()) {
                        addChip(label) {
                            appendClipboardText(all, item)
                            showClipboard = false
                        }
                    }
                }
            }
            return
        }

        Calculator.calculate(tok)?.let { addChip("= $it") { replaceToken(it) } }

        if (mode == KeyboardMode.NORMAL && !thinking && latestAiAnswers.isEmpty()) {
            WordSuggestions.suggest(all).forEach { word ->
                addChip(word) { replaceToken(word) }
            }
        }

        if (all.isNotBlank() && mode == KeyboardMode.NORMAL) {
            addChip("Rewrite") { requestAiAction(AiAction.REWRITE, all) }
            addChip("Explain") { requestAiAction(AiAction.EXPLAIN, all) }
        }

        if (thinking) {
            addChip("Thinking...") {}
        } else if (latestAiAnswers.isNotEmpty()) {
            latestAiAnswers.take(MAX_AI_ANSWERS).forEach { answer ->
                addChip(answer) {
                    replaceAll(all, answer)
                    latestAiAnswers = emptyList()
                    aiError = null
                }
            }
        } else if (!aiError.isNullOrBlank()) {
            addChip(aiError!!) {}
        } else if (QuestionEngine.isQuestion(all) && mode == KeyboardMode.NORMAL) {
            addChip("AI ready") { updateQuestionDetection() }
        }

        if (all.isNotEmpty() && mode != KeyboardMode.NORMAL) {
            val transformed = transformAll(all)
            if (transformed != all) addChip(transformed) { replaceAll(all, transformed) }
        }

        if (suggestions.childCount <= 3) addChip("Type to get word suggestions") {}
    }

    private fun requestAiAction(action: AiAction, text: String) {
        if (!deviceAllowed) return
        val cleanText = text.trim()
        if (cleanText.isEmpty() || mode != KeyboardMode.NORMAL) return

        pendingRequest?.cancel(true)
        pendingRequest = null
        val thisRequest = ++requestNumber
        aiAction = action
        latestAiAnswers = emptyList()
        aiError = null
        updateSuggestions(thinking = true)

        val prompt = when (action) {
            AiAction.REWRITE ->
                "Rewrite the following text to be clearer, natural and grammatically correct. " +
                "Return only the rewritten text. Do not explain it. Do not use tool calls. " +
                "Text: $cleanText"
            AiAction.EXPLAIN ->
                "Explain the following text simply and clearly in a short answer. " +
                "Return only the explanation. Do not use tool calls or safety labels. " +
                "Text: $cleanText"
            AiAction.QUESTION -> cleanText
        }

        pendingRequest = debounceExecutor.schedule({
            networkExecutor.execute {
                val result = askBackendWithRetry(prompt)
                mainHandler.post {
                    if (thisRequest != requestNumber) return@post
                    latestAiAnswers = result.answer?.let { parseAnswers(it) }.orEmpty()
                    aiError = if (latestAiAnswers.isEmpty() && result.error == null) {
                        "No usable answer"
                    } else {
                        result.error
                    }
                    updateSuggestions()
                }
            }
        }, 100L, TimeUnit.MILLISECONDS)
    }

    private fun rememberClipboard() {
        try {
            val clip = clipboardManager.primaryClip ?: return
            if (clip.itemCount <= 0) return
            val text = clip.getItemAt(0)
                .coerceToText(this)
                ?.toString()
                ?.trim()
                .orEmpty()
            if (text.isBlank()) return

            clipboardItems.removeAll { it == text }
            clipboardItems.add(0, text)
            while (clipboardItems.size > 12) {
                clipboardItems.removeAt(clipboardItems.lastIndex)
            }
        } catch (_: SecurityException) {
            // Some Android versions restrict clipboard reads. Keep the keyboard alive.
        } catch (_: Exception) {}
    }

    private fun cycleMode() {
        if (!deviceAllowed) return
        // Change only the state during the key/click callback. Do not mutate the
        // suggestion view hierarchy while Android is dispatching that callback.
        pendingRequest?.cancel(true)
        pendingRequest = null
        requestNumber++

        val values = KeyboardMode.values()
        mode = values[(mode.ordinal + 1) % values.size]
        generatedUnits.clear()
        latestAiAnswers = emptyList()
        aiError = null
        aiAction = AiAction.QUESTION
        showClipboard = false

        // Refresh only after the touch dispatch has completely returned.
        scheduleSuggestionRefresh()
    }

    private fun addChip(label: String, action: () -> Unit) {
        val b = Button(this).apply {
            text = label
            textSize = 13f
            isAllCaps = false
            setTextColor(keyText)
            gravity = Gravity.CENTER
            minHeight = 0; minimumHeight = 0; minWidth = 0; minimumWidth = 0
            includeFontPadding = false
            setPadding(dp(8), 0, dp(8), 0)
            background = GradientDrawable().apply { setColor(suggestionBg); cornerRadius = dp(9).toFloat() }
            stateListAnimator = null
            setOnClickListener {
                if (!deviceAllowed) {
                    updateSuggestions()
                    return@setOnClickListener
                }
                try { action() } catch (_: Exception) {}
            }
        }
        suggestions.addView(b, LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, dp(38)).apply {
            setMargins(dp(2), dp(1), dp(2), dp(1))
        })
    }

    private fun commitTypedKey(value: String) {
        when (value) {
            "__TORACOKEY_INSERT_TIME__" -> {
                generatedUnits.clear()
                safeCommit(SimpleDateFormat("h:mm a", Locale.getDefault()).format(Date()))
                scheduleSuggestionRefresh()
                return
            }
            "__TORACOKEY_INSERT_DATE__" -> {
                generatedUnits.clear()
                safeCommit(SimpleDateFormat("dd/MM/yyyy", Locale.getDefault()).format(Date()))
                scheduleSuggestionRefresh()
                return
            }
        }

        if (value == "\b") {
            deleteByTypingMode()
            return
        }

        if (value == " " || value.length != 1 || !value[0].isLetter()) {
            generatedUnits.clear()
            safeCommit(value)
            return
        }

        val ch = value[0]
        val ic = currentInputConnection ?: return

        try {
            ic.beginBatchEdit()

            val output: String
            val generatedLength: Int

            when (mode) {
                KeyboardMode.NORMAL,
                KeyboardMode.REVERSE -> {
                    output = ch.toString()
                    generatedLength = 1
                }

                KeyboardMode.MONO -> {
                    output = "$ch "
                    generatedLength = output.length
                }

                KeyboardMode.DOUBLE -> {
                    output = "$ch$ch "
                    generatedLength = output.length
                }

                KeyboardMode.ALT_CASE -> {
                    val before = editorText()
                    val letters = before.count { it.isLetter() }
                    val out =
                        if (letters % 2 == 0)
                            ch.lowercaseChar()
                        else
                            ch.uppercaseChar()

                    output = out.toString()
                    generatedLength = 1
                }

                KeyboardMode.SPACED_DOUBLE -> {
                    output = "$ch $ch "
                    generatedLength = output.length
                }

                KeyboardMode.HELLO -> {
                    // HELLO mode: every typed letter becomes two
                    // consecutive copies with no added spaces.
                    // Example: h -> hh, e -> ee, l -> ll.
                    output = "$ch$ch"
                    generatedLength = 2
                }
            }

            ic.commitText(output, 1)

            // Only special/generated typing needs grouped backspace
            // history. Normal modes behave like ordinary typing.
            if (
                mode == KeyboardMode.MONO ||
                mode == KeyboardMode.DOUBLE ||
                mode == KeyboardMode.SPACED_DOUBLE ||
                mode == KeyboardMode.HELLO
            ) {
                generatedUnits.addLast(generatedLength)
            } else {
                generatedUnits.clear()
            }

        } catch (_: Exception) {
            try {
                ic.commitText(ch.toString(), 1)
                generatedUnits.clear()
            } catch (_: Exception) {}
        } finally {
            try { ic.endBatchEdit() } catch (_: Exception) {}
        }
    }

    private fun deleteByTypingMode() {
        if (
            mode == KeyboardMode.MONO ||
            mode == KeyboardMode.DOUBLE ||
            mode == KeyboardMode.SPACED_DOUBLE ||
            mode == KeyboardMode.HELLO
        ) {
            val count =
                if (generatedUnits.isEmpty()) {
                    // If the keyboard has no history (for example after
                    // reopening the input field), remove one character
                    // rather than making an unsafe large deletion.
                    1
                } else {
                    generatedUnits.removeLast()
                }

            safeDelete(count)
        } else {
            safeDelete(1)
        }
    }

    private fun replaceToken(value: String) {
        if (!deviceAllowed) return
        generatedUnits.clear()
        val all = editorText()
        val token = all.substringAfterLast(" ")

        if (token.isNotEmpty()) {
            safeDelete(token.length)
        }

        // Commit the selected suggestion as a complete word and
        // leave a space for the next word. This prevents the next
        // typed word from replacing the selected suggestion.
        safeCommit(value.trimEnd() + " ")
        scheduleSuggestionRefresh()
        scheduleQuestionDetection()
    }

    private fun appendClipboardText(
        existing: String,
        clipboardText: String
    ) {
        if (!deviceAllowed) return
        generatedUnits.clear()
        val value = clipboardText.trim()
        if (value.isEmpty()) return

        // Clipboard text is ADDED after the current context.
        // Example:
        // "they are going to" + "school"
        // -> "they are going to school"
        val separator =
            if (existing.isNotEmpty() &&
                !existing.last().isWhitespace()
            ) {
                " "
            } else {
                ""
            }

        safeCommit(separator + value)
        scheduleSuggestionRefresh()
        scheduleQuestionDetection()
    }

    private fun replaceAll(old: String, value: String) {
        if (!deviceAllowed) return
        generatedUnits.clear()
        if (old.isNotEmpty()) safeDelete(old.length)
        safeCommit(value)
        updateQuestionDetection()
    }

    private fun transformVoiceText(input: String, selectedMode: KeyboardMode): String = when (selectedMode) {
        KeyboardMode.NORMAL, KeyboardMode.REVERSE -> input + " "
        KeyboardMode.MONO -> input.split(" ", limit = -1).joinToString(" ") { word ->
            word.toCharArray().joinToString(" ")
        } + " "
        KeyboardMode.DOUBLE -> input.split(" ", limit = -1).joinToString(" ") { word ->
            word.toCharArray().joinToString("") { ch -> "$ch$ch " }.trimEnd()
        } + " "
        KeyboardMode.ALT_CASE -> {
            var upper = false
            buildString(input.length + 1) {
                input.forEach { ch ->
                    if (ch == ' ') { append(ch); upper = false }
                    else { append(if (upper) ch.uppercaseChar() else ch.lowercaseChar()); upper = !upper }
                }
                append(' ')
            }
        }
        KeyboardMode.SPACED_DOUBLE -> input.split(" ", limit = -1).joinToString(" ") { word ->
            word.toCharArray().joinToString(" ") { ch -> "$ch $ch" }
        } + " "
        KeyboardMode.HELLO -> input.toCharArray().joinToString("") { ch ->
            if (ch.isLetter()) "$ch$ch" else ch.toString()
        } + " "
    }

    private fun transformAll(input: String): String = when (mode) {
        KeyboardMode.NORMAL -> input
        KeyboardMode.REVERSE -> input.reversed()
        KeyboardMode.MONO -> input.split(" ", limit = -1).joinToString(" ") { it.toCharArray().joinToString(" ") }
        KeyboardMode.DOUBLE -> input.split(" ", limit = -1).joinToString(" ") { w -> w.toCharArray().joinToString(" ") { ch -> "$ch$ch" } }
        KeyboardMode.ALT_CASE -> {
            var upper = false
            buildString(input.length) { input.forEach { ch ->
                if (ch == ' ') { append(ch); upper = false }
                else { append(if (upper) ch.uppercaseChar() else ch.lowercaseChar()); upper = !upper }
            }}
        }
        KeyboardMode.SPACED_DOUBLE -> input.split(" ", limit = -1).joinToString(" ") { w -> w.toCharArray().joinToString(" ") { ch -> "$ch $ch" } }
        KeyboardMode.HELLO -> input.toCharArray().joinToString("") { ch ->
            if (ch.isLetter()) "$ch$ch" else ch.toString()
        }
    }

    private fun parseAnswers(raw: String): List<String> {
        val cleaned = raw
            .replace("\\r", "")
            .replace(Regex("(?s)<tool_call_start>.*?<tool_call_end>"), "")
            .replace(Regex("(?s)\\[tool_call_start\\].*?\\[tool_call_end\\]"), "")
            .replace(Regex("(?s)\\|<tool_call_start>.*?\\|<tool_call_end>"), "")
            .trim()

        return cleaned
            .split("\\n", "|||", "•", ";")
            .map {
                it.trim()
                    .replace(Regex("^[-*]\\s+"), "")
                    .replace(Regex("^\\d+[.)]\\s+"), "")
            }
            .filter { it.isNotBlank() }
            .filterNot { looksLikeBadAiOutput(it) }
            .distinct()
            .take(MAX_AI_ANSWERS)
    }

    private fun looksLikeBadAiOutput(text: String): Boolean {
        val q = text.lowercase()
        return q.contains("tool_call_start") ||
            q.contains("tool_call_end") ||
            q.contains("[google](") ||
            q.contains("user safety:") ||
            q.startsWith("user safety") ||
            q.contains("<tool_call")
    }

    private fun editorText(): String = try { currentInputConnection?.getTextBeforeCursor(500, 0)?.toString() ?: "" } catch (_: Exception) { "" }
    private fun safeCommit(value: String) { try { currentInputConnection?.commitText(value, 1) } catch (_: Exception) {} }
    private fun safeDelete(count: Int) { try { currentInputConnection?.deleteSurroundingText(count, 0) } catch (_: Exception) {} }

    private fun modeName() = when (mode) {
        KeyboardMode.NORMAL -> "Normal"
        KeyboardMode.REVERSE -> "Reverse"
        KeyboardMode.MONO -> "Mono"
        KeyboardMode.DOUBLE -> "Double"
        KeyboardMode.ALT_CASE -> "Alt"
        KeyboardMode.SPACED_DOUBLE -> "H H"
        KeyboardMode.HELLO -> "Hello"
    }

    private data class AiResult(val answer: String?, val error: String?)

    private fun askBackendWithRetry(question: String): AiResult {
        var last = AiResult(null, "No answer")
        repeat(2) { attempt ->
            if (Thread.currentThread().isInterrupted) return last
            last = askBackend(question)
            if (last.answer != null && !looksLikeBadAiOutput(last.answer)) return last
            if (attempt == 0) {
                try { Thread.sleep(500L) }
                catch (_: InterruptedException) { return last }
            }
        }
        return if (last.answer != null && looksLikeBadAiOutput(last.answer)) {
            AiResult(null, "AI returned an invalid response")
        } else {
            last
        }
    }

    private fun askBackend(question: String): AiResult {
        var connection: HttpURLConnection? = null
        return try {
            connection = (URL(BACKEND_URL).openConnection() as HttpURLConnection).apply {
                requestMethod = "POST"
                connectTimeout = 15_000
                readTimeout = 45_000
                doOutput = true
                useCaches = false
                setRequestProperty("Content-Type", "application/json; charset=UTF-8")
                setRequestProperty("Accept", "application/json")
                setRequestProperty("User-Agent", "ToracoKeyAI/0.37.0")
            }
            val body = JSONObject()
                .put("question", question)
                .put("deviceId", deviceControl.getInstallId())
                .toString()
            connection.outputStream.use { it.write(body.toByteArray(Charsets.UTF_8)) }
            val status = connection.responseCode
            val stream = if (status in 200..299) connection.inputStream else connection.errorStream
            val responseBody = stream?.let {
                BufferedReader(InputStreamReader(it, Charsets.UTF_8)).use { reader -> reader.readText() }
            }.orEmpty()
            if (status !in 200..299) {
                return AiResult(null, "Server error $status")
            }
            val answer = JSONObject(responseBody).optString("answer").trim()
            if (answer.isNotBlank() && !looksLikeBadAiOutput(answer)) AiResult(answer, null)
            else AiResult(null, "Invalid AI response")
        } catch (e: Exception) {
            val message = e.message?.take(32)?.replace("\n", " ") ?: "Network error"
            AiResult(null, message)
        } finally {
            connection?.disconnect()
        }
    }

    private fun checkDeviceAuthorization() {
        if (authorizationCheckRunning) return
        authorizationCheckRunning = true
        authorizationExecutor.execute {
            val result = try {
                deviceControl.check()
            } catch (_: Exception) {
                DeviceControl.Result(false, "offline", "Connect to the internet to verify this installation")
            } finally {
                authorizationCheckRunning = false
            }
            mainHandler.post {
                deviceAllowed = result.allowed
                deviceStatus = result.status
                deviceMessage = when (result.status) {
                    "blocked" -> "This installation has been blocked by the administrator"
                    "pending" -> "Waiting for administrator authorization"
                    "offline" -> result.message
                    "authorized_cached" -> "Authorized"
                    else -> result.message.ifBlank { "Authorized" }
                }
                if (!deviceAllowed) {
                    pendingRequest?.cancel(true)
                    pendingRequest = null
                    requestNumber++
                    stopSpeechRecognizer()
                    latestAiAnswers = emptyList()
                    aiError = null
                    showClipboard = false
                }
                if (::suggestions.isInitialized) updateSuggestions()
            }
        }
    }

    override fun onDestroy() {
        stopSpeechRecognizer()
        try { unregisterReceiver(voicePermissionReceiver) } catch (_: Exception) {}
        try { clipboardManager.removePrimaryClipChangedListener(clipboardListener) } catch (_: Exception) {}
        pendingRequest?.cancel(true)
        pendingRequest = null
        requestNumber++
        try { debounceExecutor.shutdownNow() } catch (_: Exception) {}
        try { networkExecutor.shutdownNow() } catch (_: Exception) {}
        try { authorizationExecutor.shutdownNow() } catch (_: Exception) {}
        authorizationHandler.removeCallbacksAndMessages(null)
        mainHandler.removeCallbacksAndMessages(null)
        voiceInputConnection = null
        super.onDestroy()
    }

    private fun dp(v: Int) = (v * resources.displayMetrics.density).toInt()
}

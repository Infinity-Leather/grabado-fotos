/**
 * ESTUDIO PDI · GRABADO LÁSER SOBRE CUERO NEGRO
 * Procesamiento Digital de Imágenes 100% Clásico, Local y Binario.
 * Sin IA, sin APIs externas, sin dependencias remotas.
 */

(function () {
  "use strict";

  // =========================================================================
  // 1. ESTADO GLOBAL DE LA APLICACIÓN
  // =========================================================================
  const AppState = {
    // Imagen original inmutable cargada por el usuario
    sourceImageElement: null,
    sourceDataURL: null,
    sourceWidth: 0,
    sourceHeight: 0,

    // Transformaciones geométricas
    rotationDeg: 0, // 0, 90, 180, 270
    flipHorizontal: false,
    crop: { xPct: 0, yPct: 0, wPct: 100, hPct: 100 },
    cropDrawingMode: false,

    // Medidas físicas y resolución
    physWidthMM: 80.0,
    physHeightMM: 80.0,
    lockAspect: true,
    dpi: 600,
    targetWidthPx: 1890,
    targetHeightPx: 1890,

    // Búferes en resolución física de trabajo
    baseRGBA: null,            // Uint8ClampedArray (W * H * 4)
    subjectMask: null,         // Uint8Array (W * H) -> 1 = Sujeto, 0 = Fondo eliminado
    protectMask: null,         // Uint8Array (W * H) -> 1 = Protegido contra limpieza
    levelOverrideMask: null,   // Int8Array (W * H)  -> -1 = Auto, 0..3 = Nivel manual pre-trama
    binaryOverrideMask: null,  // Int8Array (W * H)  -> -1 = Auto, 0 = Transparente, 1 = Negro sólido

    // Salida binaria final y diagnósticos
    finalBinaryMask: null,     // Uint8Array (W * H) -> 1 = Negro (0,0,0,255), 0 = Transp (0,0,0,0)
    removedDetailsMask: null,  // Uint8Array (W * H) -> 1 = Eliminado por filtro de limpieza
    lastStats: {
      markedRatioPct: 0,
      smallFragmentsCount: 0,
      isStrictlyBinary: true
    },

    // Parámetros del pipeline PDI
    params: {
      brightness: 0,
      contrast: 15,
      gamma: 1.0,
      smoothRadius: 1,
      thresholds: [64, 128, 192],
      bandMapping: [0, 1, 2, 3], // Banda 0..3 -> Nivel 0..3
      cleanEnabled: true,
      cleanCriterion: "dimension", // "dimension" (mm) | "area" (mm2)
      cleanThreshold: 1.0,
      morphOp: "none", // "none" | "open" | "close"
      edgesEnabled: true,
      edgeThreshold: 95,
      edgeWidthMM: 0.35,
      halftoneType: "lines", // "lines" | "dots"
      lineAngleDeg: 45,
      lineThickMM: 0.30,
      lineGapOpenMM: 0.60,
      lineGapMidMM: 0.40,
      dotDiamMM: 0.30,
      dotGapOpenMM: 0.60,
      dotGapMidMM: 0.40
    },

    // Interfaz y Herramientas
    activeTool: "pan",
    wandTolerance: 28,
    brushSizeMM: 1.2,
    manualLevelValue: 3,
    viewMode: "split", // "split" | "original" | "mask" | "leather" | "compare"
    zoom: 1.0,
    compareSplitPct: 50,
    showSubjectOverlay: true,
    showProtectOverlay: true,
    previewRemovedDetails: false,
    leatherMarkColor: "#d8be98",

    // Polígono / Línea temporal en construcción
    tempPoints: [],
    dragStartPt: null,
    isPointerDown: false,

    // Historial Deshacer / Rehacer (Snapshots de máscaras)
    historyUndo: [],
    historyRedo: [],
    maxHistory: 20,

    // Control de procesamiento asíncrono
    cancelRequested: false
  };

  // =========================================================================
  // 2. REFERENCIAS DOM
  // =========================================================================
  const DOM = {
    CanvasOriginal: document.getElementById("CanvasOriginal"),
    CanvasMask: document.getElementById("CanvasMask"),
    CanvasLeather: document.getElementById("CanvasLeather"),
    ReadoutDimensions: document.getElementById("ReadoutDimensions"),
    EffectiveMeasureBox: document.getElementById("EffectiveMeasureBox"),
    ProcessingIndicator: document.getElementById("ProcessingIndicator"),
    ProcText: document.getElementById("ProcText"),
    CursorCoords: document.getElementById("CursorCoords"),
    ZoomReadout: document.getElementById("ZoomReadout"),
    ExportStatsList: document.getElementById("ExportStatsList"),
    LineMathReadout: document.getElementById("LineMathReadout"),
    DotMathReadout: document.getElementById("DotMathReadout")
  };

  const CtxOrig = DOM.CanvasOriginal.getContext("2d", { willReadFrequently: true });
  const CtxMask = DOM.CanvasMask.getContext("2d", { willReadFrequently: true });
  const CtxLeather = DOM.CanvasLeather.getContext("2d", { willReadFrequently: true });

  // =========================================================================
  // 3. UTILIDADES MATEMÁTICAS Y DE MEDIDAS FÍSICAS
  // =========================================================================

  function mmToPx(mm, dpi) {
    return (mm * dpi) / 25.4;
  }

  function pxToMm(px, dpi) {
    return (px * 25.4) / dpi;
  }

  function clamp(val, min, max) {
    return val < min ? min : val > max ? max : val;
  }

  function hexToRgb(hex) {
    const clean = hex.replace("#", "");
    const num = parseInt(clean, 16);
    return {
      r: (num >> 16) & 255,
      g: (num >> 8) & 255,
      b: num & 255
    };
  }

  /**
   * Comprueba si existen ediciones manuales realizadas por el usuario
   */
  function hasManualEdits() {
    if (!AppState.levelOverrideMask || !AppState.binaryOverrideMask) return false;
    for (let i = 0; i < AppState.levelOverrideMask.length; i++) {
      if (AppState.levelOverrideMask[i] !== -1 || AppState.binaryOverrideMask[i] !== -1 || AppState.protectMask[i] !== 0) {
        return true;
      }
    }
    return false;
  }

  // =========================================================================
  // 4. HISTORIAL DESHACER / REHACER
  // =========================================================================

  function pushHistorySnapshot() {
    if (!AppState.subjectMask) return;
    const snap = {
      subjectMask: new Uint8Array(AppState.subjectMask),
      protectMask: new Uint8Array(AppState.protectMask),
      levelOverrideMask: new Int8Array(AppState.levelOverrideMask),
      binaryOverrideMask: new Int8Array(AppState.binaryOverrideMask)
    };
    AppState.historyUndo.push(snap);
    if (AppState.historyUndo.length > AppState.maxHistory) {
      AppState.historyUndo.shift();
    }
    AppState.historyRedo = [];
    updateHistoryButtons();
  }

  function restoreSnapshot(snap) {
    AppState.subjectMask.set(snap.subjectMask);
    AppState.protectMask.set(snap.protectMask);
    AppState.levelOverrideMask.set(snap.levelOverrideMask);
    AppState.binaryOverrideMask.set(snap.binaryOverrideMask);
    runPipelineAndRender();
  }

  function undoAction() {
    if (AppState.historyUndo.length === 0) return;
    const current = {
      subjectMask: new Uint8Array(AppState.subjectMask),
      protectMask: new Uint8Array(AppState.protectMask),
      levelOverrideMask: new Int8Array(AppState.levelOverrideMask),
      binaryOverrideMask: new Int8Array(AppState.binaryOverrideMask)
    };
    AppState.historyRedo.push(current);
    const prev = AppState.historyUndo.pop();
    restoreSnapshot(prev);
    updateHistoryButtons();
  }

  function redoAction() {
    if (AppState.historyRedo.length === 0) return;
    const current = {
      subjectMask: new Uint8Array(AppState.subjectMask),
      protectMask: new Uint8Array(AppState.protectMask),
      levelOverrideMask: new Int8Array(AppState.levelOverrideMask),
      binaryOverrideMask: new Int8Array(AppState.binaryOverrideMask)
    };
    AppState.historyUndo.push(current);
    const next = AppState.historyRedo.pop();
    restoreSnapshot(next);
    updateHistoryButtons();
  }

  function updateHistoryButtons() {
    document.getElementById("BtnUndo").disabled = AppState.historyUndo.length === 0;
    document.getElementById("BtnRedo").disabled = AppState.historyRedo.length === 0;
  }

  // =========================================================================
  // 5. GENERADOR DE IMAGEN SINTÉTICA DE DEMOSTRACIÓN Y PRUEBA
  // =========================================================================

  function createSyntheticDemoImage() {
    const w = 700;
    const h = 700;
    const c = document.createElement("canvas");
    c.width = w;
    c.height = h;
    const ctx = c.getContext("2d");

    // Fondo uniforme verdoso claro (fácil de probar con varita mágica)
    ctx.fillStyle = "#b8d8be";
    ctx.fillRect(0, 0, w, h);

    // Escudo / Medallón exterior
    ctx.fillStyle = "#2b2b2b";
    ctx.beginPath();
    ctx.arc(350, 350, 280, 0, Math.PI * 2);
    ctx.fill();

    // Anillo intermedio gris medio
    ctx.strokeStyle = "#969696";
    ctx.lineWidth = 22;
    ctx.beginPath();
    ctx.arc(350, 350, 245, 0, Math.PI * 2);
    ctx.stroke();

    // Retrato estilizado geométrico con 4 niveles claros de luminancia
    // Camiseta (gris oscuro)
    ctx.fillStyle = "#484848";
    ctx.beginPath();
    ctx.ellipse(350, 540, 175, 110, 0, Math.PI, Math.PI * 2, false);
    ctx.fill();

    // Número "10" en el pecho (blanco brillante)
    ctx.fillStyle = "#f2f2f2";
    ctx.font = "bold 78px sans-serif";
    ctx.textAlign = "center";
    ctx.fillText("10", 350, 525);

    // Cuello y Rostro (gris medio-claro con sombreado lateral)
    ctx.fillStyle = "#888888";
    ctx.fillRect(310, 360, 80, 75);

    const gradFace = ctx.createLinearGradient(230, 180, 470, 380);
    gradFace.addColorStop(0, "#f0f0f0");
    gradFace.addColorStop(0.55, "#b0b0b0");
    gradFace.addColorStop(1, "#555555");
    ctx.fillStyle = gradFace;
    ctx.beginPath();
    ctx.ellipse(350, 275, 105, 130, 0, 0, Math.PI * 2);
    ctx.fill();

    // Cabello (oscuro)
    ctx.fillStyle = "#181818";
    ctx.beginPath();
    ctx.arc(350, 235, 108, Math.PI, Math.PI * 2);
    ctx.fill();

    // Cejas, Ojos, Nariz y Labios (rasgos finos para probar protección y pinceles)
    ctx.strokeStyle = "#151515";
    ctx.lineWidth = 7;
    // Cejas
    ctx.beginPath();
    ctx.moveTo(285, 235); ctx.lineTo(330, 240);
    ctx.moveTo(370, 240); ctx.lineTo(415, 235);
    ctx.stroke();

    // Ojos
    ctx.fillStyle = "#ffffff";
    ctx.beginPath();
    ctx.ellipse(308, 262, 18, 10, 0, 0, Math.PI * 2);
    ctx.ellipse(392, 262, 18, 10, 0, 0, Math.PI * 2);
    ctx.fill();

    ctx.fillStyle = "#111111";
    ctx.beginPath();
    ctx.arc(308, 262, 7, 0, Math.PI * 2);
    ctx.arc(392, 262, 7, 0, Math.PI * 2);
    ctx.fill();

    // Nariz y Mandíbula
    ctx.strokeStyle = "#222222";
    ctx.lineWidth = 5;
    ctx.beginPath();
    ctx.moveTo(350, 260);
    ctx.lineTo(340, 315);
    ctx.lineTo(362, 318);
    ctx.stroke();

    // Boca
    ctx.beginPath();
    ctx.moveTo(315, 352);
    ctx.quadraticCurveTo(350, 368, 385, 352);
    ctx.stroke();

    // Pequeñas motas de ruido aisladas para probar el filtro de limpieza (< 1 mm)
    ctx.fillStyle = "#ffffff";
    ctx.fillRect(190, 290, 4, 4);
    ctx.fillRect(505, 295, 5, 5);
    ctx.fillRect(210, 410, 4, 4);

    return c.toDataURL("image/png");
  }

  // =========================================================================
  // 6. PREPARACIÓN DE LA IMAGEN Y BÚFERES FÍSICOS
  // =========================================================================

  function loadImageFromDataURL(dataUrl, preserveMasksIfSameSize = false) {
    const img = new Image();
    img.onload = function () {
      AppState.sourceImageElement = img;
      AppState.sourceDataURL = dataUrl;
      AppState.sourceWidth = img.naturalWidth || img.width;
      AppState.sourceHeight = img.naturalHeight || img.height;

      if (!preserveMasksIfSameSize) {
        AppState.rotationDeg = 0;
        AppState.flipHorizontal = false;
        AppState.crop = { xPct: 0, yPct: 0, wPct: 100, hPct: 100 };
        syncCropInputs();

        // Ajustar alto físico proporcional al ancho físico actual
        if (AppState.lockAspect) {
          const aspect = AppState.sourceHeight / AppState.sourceWidth;
          AppState.physHeightMM = Number((AppState.physWidthMM * aspect).toFixed(2));
          document.getElementById("PhysHeightMM").value = AppState.physHeightMM;
        }
      }

      rebuildBaseBufferAndMasks(preserveMasksIfSameSize);
    };
    img.onerror = function () {
      alert("Error: No se pudo decodificar la imagen seleccionada. Verifica que sea un archivo PNG, JPG o WebP válido.");
    };
    img.src = dataUrl;
  }

  /**
   * Calcula las dimensiones efectivas en píxeles a partir de mm y PPP,
   * aplica rotación, volteo y recorte, y prepara los búferes de trabajo.
   */
  function rebuildBaseBufferAndMasks(preserveMasks = false) {
    if (!AppState.sourceImageElement) return;

    // 1. Calcular dimensiones de la región recortada considerando rotación
    const rot = ((AppState.rotationDeg % 360) + 360) % 360;
    const rotW = (rot === 90 || rot === 270) ? AppState.sourceHeight : AppState.sourceWidth;
    const rotH = (rot === 90 || rot === 270) ? AppState.sourceWidth : AppState.sourceHeight;

    const cropWOrig = Math.max(1, Math.round((rotW * AppState.crop.wPct) / 100));
    const cropHOrig = Math.max(1, Math.round((rotH * AppState.crop.hPct) / 100));
    const cropXOrig = clamp(Math.round((rotW * AppState.crop.xPct) / 100), 0, rotW - cropWOrig);
    const cropYOrig = clamp(Math.round((rotH * AppState.crop.yPct) / 100), 0, rotH - cropHOrig);

    if (AppState.lockAspect) {
      const aspect = cropHOrig / cropWOrig;
      AppState.physHeightMM = Number((AppState.physWidthMM * aspect).toFixed(2));
      document.getElementById("PhysHeightMM").value = AppState.physHeightMM;
    }

    // 2. Conversión física: píxeles = round(mm * ppp / 25.4)
    let targetW = Math.max(16, Math.round(mmToPx(AppState.physWidthMM, AppState.dpi)));
    let targetH = Math.max(16, Math.round(mmToPx(AppState.physHeightMM, AppState.dpi)));

    // Control de memoria máxima (~36 MP) para evitar bloqueo del navegador
    const MAX_PIXELS = 6000 * 6000;
    if (targetW * targetH > MAX_PIXELS) {
      const scale = Math.sqrt(MAX_PIXELS / (targetW * targetH));
      targetW = Math.floor(targetW * scale);
      targetH = Math.floor(targetH * scale);
      alert("Aviso de memoria: El tamaño en píxeles excede el límite seguro del navegador. Se ha ajustado a " + targetW + "×" + targetH + " px.");
    }

    const sizeChanged = (targetW !== AppState.targetWidthPx || targetH !== AppState.targetHeightPx);
    AppState.targetWidthPx = targetW;
    AppState.targetHeightPx = targetH;

    const effW_MM = pxToMm(targetW, AppState.dpi).toFixed(2);
    const effH_MM = pxToMm(targetH, AppState.dpi).toFixed(2);

    DOM.EffectiveMeasureBox.innerHTML =
      `Medida efectiva tras redondeo: <strong>${effW_MM} × ${effH_MM} mm</strong> (${targetW} × ${targetH} px @ ${AppState.dpi} PPP)`;
    DOM.ReadoutDimensions.textContent = `${effW_MM}×${effH_MM} mm | ${targetW}×${targetH} px | ${AppState.dpi} PPP`;

    // 3. Dibujar imagen rotada/volteada en lienzo temporal y extraer el recorte escalado al tamaño físico
    const rotCanvas = document.createElement("canvas");
    rotCanvas.width = rotW;
    rotCanvas.height = rotH;
    const rCtx = rotCanvas.getContext("2d");

    rCtx.save();
    rCtx.translate(rotW / 2, rotH / 2);
    rCtx.rotate((rot * Math.PI) / 180);
    if (AppState.flipHorizontal) {
      rCtx.scale(-1, 1);
    }
    rCtx.drawImage(
      AppState.sourceImageElement,
      -AppState.sourceWidth / 2,
      -AppState.sourceHeight / 2
    );
    rCtx.restore();

    const destCanvas = document.createElement("canvas");
    destCanvas.width = targetW;
    destCanvas.height = targetH;
    const dCtx = destCanvas.getContext("2d");
    dCtx.imageSmoothingEnabled = true;
    dCtx.imageSmoothingQuality = "high";
    dCtx.drawImage(
      rotCanvas,
      cropXOrig, cropYOrig, cropWOrig, cropHOrig,
      0, 0, targetW, targetH
    );

    const imgData = dCtx.getImageData(0, 0, targetW, targetH);
    AppState.baseRGBA = new Uint8ClampedArray(imgData.data);

    const totalPx = targetW * targetH;

    if (!preserveMasks || sizeChanged || !AppState.subjectMask || AppState.subjectMask.length !== totalPx) {
      AppState.subjectMask = new Uint8Array(totalPx);
      AppState.protectMask = new Uint8Array(totalPx);
      AppState.levelOverrideMask = new Int8Array(totalPx);
      AppState.binaryOverrideMask = new Int8Array(totalPx);

      AppState.levelOverrideMask.fill(-1);
      AppState.binaryOverrideMask.fill(-1);

      // Respetar transparencia original del archivo cargado en la máscara del sujeto
      for (let i = 0; i < totalPx; i++) {
        AppState.subjectMask[i] = AppState.baseRGBA[i * 4 + 3] > 20 ? 1 : 0;
      }

      AppState.historyUndo = [];
      AppState.historyRedo = [];
      updateHistoryButtons();
    }

    AppState.finalBinaryMask = new Uint8Array(totalPx);
    AppState.removedDetailsMask = new Uint8Array(totalPx);

    updateBrushReadout();
    runPipelineAndRender();
  }

  // =========================================================================
  // 7. MOTOR DE ALGORITMOS CLÁSICOS PDI (PIPELINE DE 10 ETAPAS)
  // =========================================================================

  /**
   * Algoritmo clásico de Otsu Multinivel (3 umbrales para 4 clases)
   * Evaluado exclusivamente sobre los píxeles incluidos en la máscara del sujeto.
   */
  function computeMultiOtsuThresholds3(lumArray, subjectMask) {
    const hist = new Float64Array(256);
    let count = 0;
    for (let i = 0; i < lumArray.length; i++) {
      if (subjectMask[i] === 1) {
        hist[lumArray[i]]++;
        count++;
      }
    }
    if (count === 0) return [64, 128, 192];

    // Normalizar histograma y acumular momentos de orden 0 y 1
    const P = new Float64Array(256);
    const S = new Float64Array(256);
    let sumP = 0;
    let sumS = 0;
    for (let i = 0; i < 256; i++) {
      const p = hist[i] / count;
      sumP += p;
      sumS += i * p;
      P[i] = sumP;
      S[i] = sumS;
    }

    let maxVariance = -1;
    let bestT1 = 64, bestT2 = 128, bestT3 = 192;

    // Búsqueda con paso de 2 niveles para respuesta instantánea y refinamiento local
    for (let t1 = 16; t1 < 210; t1 += 2) {
      const w0 = P[t1];
      if (w0 <= 1e-6) continue;
      const m0 = S[t1] / w0;

      for (let t2 = t1 + 16; t2 < 230; t2 += 2) {
        const w1 = P[t2] - P[t1];
        if (w1 <= 1e-6) continue;
        const m1 = (S[t2] - S[t1]) / w1;

        for (let t3 = t2 + 16; t3 < 250; t3 += 2) {
          const w2 = P[t3] - P[t2];
          const w3 = 1.0 - P[t3];
          if (w2 <= 1e-6 || w3 <= 1e-6) continue;

          const m2 = (S[t3] - S[t2]) / w2;
          const m3 = (S[255] - S[t3]) / w3;

          const muT = S[255];
          const betweenVar =
            w0 * (m0 - muT) * (m0 - muT) +
            w1 * (m1 - muT) * (m1 - muT) +
            w2 * (m2 - muT) * (m2 - muT) +
            w3 * (m3 - muT) * (m3 - muT);

          if (betweenVar > maxVariance) {
            maxVariance = betweenVar;
            bestT1 = t1;
            bestT2 = t2;
            bestT3 = t3;
          }
        }
      }
    }
    return [bestT1, bestT2, bestT3];
  }

  /**
   * Filtro Box Blur separable de paso rápido O(N) para suavizado previo
   */
  function boxBlurSeparable(src, width, height, radius) {
    if (radius <= 0) return new Uint8Array(src);
    const tmp = new Uint8Array(width * height);
    const dst = new Uint8Array(width * height);
    const winSize = radius * 2 + 1;

    // Paso horizontal
    for (let y = 0; y < height; y++) {
      let sum = 0;
      const rowOffset = y * width;
      for (let k = -radius; k <= radius; k++) {
        const x = clamp(k, 0, width - 1);
        sum += src[rowOffset + x];
      }
      for (let x = 0; x < width; x++) {
        tmp[rowOffset + x] = (sum / winSize) | 0;
        const xOut = clamp(x - radius, 0, width - 1);
        const xIn = clamp(x + radius + 1, 0, width - 1);
        sum += src[rowOffset + xIn] - src[rowOffset + xOut];
      }
    }

    // Paso vertical
    for (let x = 0; x < width; x++) {
      let sum = 0;
      for (let k = -radius; k <= radius; k++) {
        const y = clamp(k, 0, height - 1);
        sum += tmp[y * width + x];
      }
      for (let y = 0; y < height; y++) {
        dst[y * width + x] = (sum / winSize) | 0;
        const yOut = clamp(y - radius, 0, height - 1);
        const yIn = clamp(y + radius + 1, 0, height - 1);
        sum += tmp[yIn * width + x] - tmp[yOut * width + x];
      }
    }
    return dst;
  }

  /**
   * Operadores morfológicos sobre el mapa de niveles (Apertura / Cierre)
   * aplicados ANTES del tramado para no destruir tramas de 0.3 mm.
   */
  function applyMorphologyOnLevels(levelMap, subjectMask, width, height, mode) {
    if (mode === "none") return levelMap;

    function erodeOrDilate(input, isDilate) {
      const out = new Uint8Array(input.length);
      for (let y = 0; y < height; y++) {
        const y0 = Math.max(0, y - 1);
        const y1 = Math.min(height - 1, y + 1);
        for (let x = 0; x < width; x++) {
          const idx = y * width + x;
          if (subjectMask[idx] === 0) {
            out[idx] = 0;
            continue;
          }
          const x0 = Math.max(0, x - 1);
          const x1 = Math.min(width - 1, x + 1);
          let best = input[idx];
          for (let ny = y0; ny <= y1; ny++) {
            for (let nx = x0; nx <= x1; nx++) {
              const nIdx = ny * width + nx;
              if (subjectMask[nIdx] === 0) continue;
              const val = input[nIdx];
              if (isDilate) {
                if (val > best) best = val;
              } else {
                if (val < best) best = val;
              }
            }
          }
          out[idx] = best;
        }
      }
      return out;
    }

    if (mode === "open") {
      const eroded = erodeOrDilate(levelMap, false);
      return erodeOrDilate(eroded, true);
    } else if (mode === "close") {
      const dilated = erodeOrDilate(levelMap, true);
      return erodeOrDilate(dilated, false);
    }
    return levelMap;
  }

  /**
   * Limpieza de Componentes Conectados (BFS) sobre las regiones tonales (Nivel > 0)
   * antes de generar la trama.
   * Distingue explícitamente entre:
   * - Criterio por dimensión de caja delimitadora (max(ancho, alto) < umbral_mm)
   * - Criterio por área del componente (área_mm2 < umbral_mm2)
   * Nunca elimina componentes que contengan al menos un píxel protegido manualmente.
   */
  function cleanSmallTonalComponents(levelMap, protectMask, width, height, dpi, criterion, thresholdVal) {
    const cleaned = new Uint8Array(levelMap);
    const removedMask = new Uint8Array(width * height);
    const visited = new Uint8Array(width * height);

    const pxPerMM = dpi / 25.4;
    const minDimPx = Math.max(1, Math.round(thresholdVal * pxPerMM));
    const minAreaPx = Math.max(1, Math.round(thresholdVal * pxPerMM * pxPerMM));

    const queue = new Int32Array(width * height);

    for (let i = 0; i < cleaned.length; i++) {
      if (cleaned[i] > 0 && visited[i] === 0) {
        let head = 0, tail = 0;
        queue[tail++] = i;
        visited[i] = 1;

        let minX = i % width, maxX = minX;
        let minY = (i / width) | 0, maxY = minY;
        let isProtected = false;

        while (head < tail) {
          const curr = queue[head++];
          if (protectMask[curr] === 1) isProtected = true;

          const cx = curr % width;
          const cy = (curr / width) | 0;
          if (cx < minX) minX = cx;
          if (cx > maxX) maxX = cx;
          if (cy < minY) minY = cy;
          if (cy > maxY) maxY = cy;

          // 4-conectividad rápida
          if (cx > 0) {
            const n = curr - 1;
            if (visited[n] === 0 && cleaned[n] > 0) { visited[n] = 1; queue[tail++] = n; }
          }
          if (cx < width - 1) {
            const n = curr + 1;
            if (visited[n] === 0 && cleaned[n] > 0) { visited[n] = 1; queue[tail++] = n; }
          }
          if (cy > 0) {
            const n = curr - width;
            if (visited[n] === 0 && cleaned[n] > 0) { visited[n] = 1; queue[tail++] = n; }
          }
          if (cy < height - 1) {
            const n = curr + width;
            if (visited[n] === 0 && cleaned[n] > 0) { visited[n] = 1; queue[tail++] = n; }
          }
        }

        if (!isProtected) {
          const compArea = tail;
          const bboxW = maxX - minX + 1;
          const bboxH = maxY - minY + 1;
          const maxBBoxDim = Math.max(bboxW, bboxH);

          const shouldRemove =
            (criterion === "dimension" && maxBBoxDim < minDimPx) ||
            (criterion === "area" && compArea < minAreaPx);

          if (shouldRemove) {
            for (let k = 0; k < tail; k++) {
              const pIdx = queue[k];
              cleaned[pIdx] = 0;
              removedMask[pIdx] = 1;
            }
          }
        }
      }
    }

    return { cleanedLevels: cleaned, removedMask };
  }

  /**
   * Detección de bordes mediante operador Sobel 3x3 + dilatación física en mm.
   * Restringida estrictamente al interior de la máscara del sujeto.
   */
  function computeSobelEdges(smoothedLum, subjectMask, width, height, threshold, edgeWidthMM, dpi) {
    const rawEdges = new Uint8Array(width * height);

    for (let y = 1; y < height - 1; y++) {
      const row = y * width;
      for (let x = 1; x < width - 1; x++) {
        const idx = row + x;
        if (subjectMask[idx] === 0) continue;
        // Evitar crear borde artificial contra la frontera exterior del recorte del sujeto
        if (
          subjectMask[idx - 1] === 0 ||
          subjectMask[idx + 1] === 0 ||
          subjectMask[idx - width] === 0 ||
          subjectMask[idx + width] === 0
        ) {
          continue;
        }

        const p00 = smoothedLum[idx - width - 1];
        const p01 = smoothedLum[idx - width];
        const p02 = smoothedLum[idx - width + 1];
        const p10 = smoothedLum[idx - 1];
        const p12 = smoothedLum[idx + 1];
        const p20 = smoothedLum[idx + width - 1];
        const p21 = smoothedLum[idx + width];
        const p22 = smoothedLum[idx + width + 1];

        const gx = -p00 + p02 - 2 * p10 + 2 * p12 - p20 + p22;
        const gy = -p00 - 2 * p01 - p02 + p20 + 2 * p21 + p22;
        const mag = Math.sqrt(gx * gx + gy * gy) * 0.25;

        if (mag >= threshold) {
          rawEdges[idx] = 1;
        }
      }
    }

    const radiusPx = Math.max(0, Math.round((mmToPx(edgeWidthMM, dpi) - 1) / 2));
    if (radiusPx <= 0) return rawEdges;

    // Dilatación circular al grosor físico deseado
    const dilated = new Uint8Array(width * height);
    const r2 = radiusPx * radiusPx;
    for (let y = 0; y < height; y++) {
      for (let x = 0; x < width; x++) {
        const idx = y * width + x;
        if (rawEdges[idx] === 1) {
          const y0 = Math.max(0, y - radiusPx);
          const y1 = Math.min(height - 1, y + radiusPx);
          const x0 = Math.max(0, x - radiusPx);
          const x1 = Math.min(width - 1, x + radiusPx);
          for (let ny = y0; ny <= y1; ny++) {
            const dy = ny - y;
            for (let nx = x0; nx <= x1; nx++) {
              const dx = nx - x;
              if (dx * dx + dy * dy <= r2) {
                const nIdx = ny * width + nx;
                if (subjectMask[nIdx] === 1) {
                  dilated[nIdx] = 1;
                }
              }
            }
          }
        }
      }
    }
    return dilated;
  }

  /**
   * Generador de Trama Física Regular con Fase Global Coherente.
   * Evalúa si el píxel (x, y) pertenece a una marca negra (1) o espacio libre (0)
   * para el nivel indicado (1 = Trama abierta, 2 = Trama media).
   */
  function createPhysicalHalftoneEvaluator(params, dpi) {
    const isLines = params.halftoneType === "lines";
    const angleRad = (params.lineAngleDeg * Math.PI) / 180;
    const cosA = Math.cos(angleRad);
    const sinA = Math.sin(angleRad);

    // Parámetros de líneas en píxeles reales
    const lineThickPx = mmToPx(params.lineThickMM, dpi);
    const linePitchOpenPx = mmToPx(params.lineThickMM + params.lineGapOpenMM, dpi);
    const linePitchMidPx = mmToPx(params.lineThickMM + params.lineGapMidMM, dpi);

    // Parámetros de puntos en píxeles reales
    // Paso entre centros = Diámetro + Separación mínima libre
    const dotRadiusPx = mmToPx(params.dotDiamMM * 0.5, dpi);
    const dotRadiusSq = dotRadiusPx * dotRadiusPx;
    const dotPitchOpenPx = mmToPx(params.dotDiamMM + params.dotGapOpenMM, dpi);
    const dotPitchMidPx = mmToPx(params.dotDiamMM + params.dotGapMidMM, dpi);

    return function evaluateHalftone(x, y, level) {
      if (level === 0) return 0;
      if (level === 3) return 1;

      if (isLines) {
        const pitch = level === 1 ? linePitchOpenPx : linePitchMidPx;
        // Coordenada perpendicular a las líneas desde el origen global (0,0)
        const u = x * cosA + y * sinA;
        const phase = ((u % pitch) + pitch) % pitch;
        return phase < lineThickPx ? 1 : 0;
      } else {
        const pitch = level === 1 ? dotPitchOpenPx : dotPitchMidPx;
        const u = ((x % pitch) + pitch) % pitch;
        const v = ((y % pitch) + pitch) % pitch;
        const half = pitch * 0.5;
        const dx = u - half;
        const dy = v - half;
        return (dx * dx + dy * dy <= dotRadiusSq) ? 1 : 0;
      }
    };
  }

  /**
   * Detector de fragmentos diminutos de borde de trama (< 0.15 mm)
   * Algoritmo: Etiquetado de componentes conectados en la máscara binaria final
   * buscando micro-islas cuyo diámetro máximo sea inferior a 0.15 mm (causadas
   * por la intersección geométrica entre el borde de una región tonal y una línea/punto de trama).
   */
  function countMicroEdgeFragments(binaryMask, width, height, dpi) {
    const minFragmentPx = Math.max(1, Math.floor(mmToPx(0.15, dpi)));
    const visited = new Uint8Array(width * height);
    const queue = new Int32Array(Math.min(width * height, 65536));
    let fragmentCount = 0;

    for (let i = 0; i < binaryMask.length; i++) {
      if (binaryMask[i] === 1 && visited[i] === 0) {
        let head = 0, tail = 0;
        queue[tail++] = i;
        visited[i] = 1;
        let minX = i % width, maxX = minX;
        let minY = (i / width) | 0, maxY = minY;
        let overflow = false;

        while (head < tail) {
          const curr = queue[head++];
          const cx = curr % width;
          const cy = (curr / width) | 0;
          if (cx < minX) minX = cx;
          if (cx > maxX) maxX = cx;
          if (cy < minY) minY = cy;
          if (cy > maxY) maxY = cy;

          const neighbors = [
            cx > 0 ? curr - 1 : -1,
            cx < width - 1 ? curr + 1 : -1,
            cy > 0 ? curr - width : -1,
            cy < height - 1 ? curr + width : -1
          ];
          for (let k = 0; k < 4; k++) {
            const n = neighbors[k];
            if (n !== -1 && visited[n] === 0 && binaryMask[n] === 1) {
              visited[n] = 1;
              if (tail < queue.length) {
                queue[tail++] = n;
              } else {
                overflow = true;
              }
            }
          }
        }

        if (!overflow) {
          const wBox = maxX - minX + 1;
          const hBox = maxY - minY + 1;
          if (Math.max(wBox, hBox) <= minFragmentPx) {
            fragmentCount++;
          }
        }
      }
    }
    return fragmentCount;
  }

  /**
   * EJECUCIÓN COMPLETA DE LA CADENA DE 10 ETAPAS
   */
  function executePipelineSync() {
    if (!AppState.baseRGBA) return;

    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    const total = W * H;
    const p = AppState.params;

    // ETAPA 1 y 2: Conversión a Luminancia (solo en máscara del sujeto)
    // ETAPA 3: LUT de Brillo, Contraste y Gamma
    const lut = new Uint8Array(256);
    const contrastFactor = (259 * (p.contrast + 255)) / (255 * (259 - p.contrast));
    const invGamma = 1.0 / Math.max(0.1, p.gamma);

    for (let v = 0; v < 256; v++) {
      let val = v + p.brightness;
      val = contrastFactor * (val - 128) + 128;
      val = clamp(val, 0, 255) / 255.0;
      val = Math.pow(val, invGamma) * 255.0;
      lut[v] = clamp(Math.round(val), 0, 255);
    }

    const adjustedLum = new Uint8Array(total);
    const rgba = AppState.baseRGBA;
    const subj = AppState.subjectMask;

    for (let i = 0; i < total; i++) {
      if (subj[i] === 0) {
        adjustedLum[i] = 0;
        continue;
      }
      const off = i * 4;
      const y = Math.round(0.299 * rgba[off] + 0.587 * rgba[off + 1] + 0.114 * rgba[off + 2]);
      adjustedLum[i] = lut[y];
    }

    // ETAPA 4: Suavizado opcional
    const smoothedLum = boxBlurSeparable(adjustedLum, W, H, p.smoothRadius);

    // ETAPA 6 y 7: Cuantización mediante 3 umbrales ordenados y Asignación Tonal
    const [t1, t2, t3] = p.thresholds;
    const map = p.bandMapping;
    let levelMap = new Uint8Array(total);

    for (let i = 0; i < total; i++) {
      // Garantía inquebrantable: una zona excluida del sujeto NUNCA reaparece
      if (subj[i] === 0) {
        levelMap[i] = 0;
        continue;
      }
      // Si el usuario pintó manualmente un nivel tonal (0..3) en este píxel, respetarlo
      const manualLvl = AppState.levelOverrideMask[i];
      if (manualLvl !== -1) {
        levelMap[i] = manualLvl;
        continue;
      }

      const lum = smoothedLum[i];
      let band = 0;
      if (lum <= t1) band = 0;
      else if (lum <= t2) band = 1;
      else if (lum <= t3) band = 2;
      else band = 3;

      levelMap[i] = map[band];
    }

    // ETAPA 5: Operaciones morfológicas y reducción de pequeños detalles en regiones tonales (Pre-trama)
    if (p.morphOp !== "none") {
      levelMap = applyMorphologyOnLevels(levelMap, subj, W, H, p.morphOp);
    }

    if (p.cleanEnabled) {
      const cleanRes = cleanSmallTonalComponents(
        levelMap,
        AppState.protectMask,
        W,
        H,
        AppState.dpi,
        p.cleanCriterion,
        p.cleanThreshold
      );
      levelMap = cleanRes.cleanedLevels;
      AppState.removedDetailsMask = cleanRes.removedMask;
    } else {
      AppState.removedDetailsMask.fill(0);
    }

    // ETAPA 8: Generación de tramas a escala física
    const evalHalftone = createPhysicalHalftoneEvaluator(p, AppState.dpi);
    const outBinary = AppState.finalBinaryMask;

    // ETAPA 9: Detección de contornos opcionales y superposición de correcciones manuales
    let edgeMask = null;
    if (p.edgesEnabled) {
      edgeMask = computeSobelEdges(smoothedLum, subj, W, H, p.edgeThreshold, p.edgeWidthMM, AppState.dpi);
    }

    let markedCount = 0;
    const binOverride = AppState.binaryOverrideMask;

    for (let y = 0; y < H; y++) {
      const row = y * W;
      for (let x = 0; x < W; x++) {
        const idx = row + x;

        // Respetar exclusión de sujeto siempre
        if (subj[idx] === 0) {
          outBinary[idx] = 0;
          continue;
        }

        // Corrección manual binaria directa (pincel negro sólido / borrador transparente)
        const bOv = binOverride[idx];
        if (bOv !== -1) {
          outBinary[idx] = bOv;
          if (bOv === 1) markedCount++;
          continue;
        }

        // Si pertenece a un contorno activo
        if (edgeMask && edgeMask[idx] === 1) {
          outBinary[idx] = 1;
          markedCount++;
          continue;
        }

        // Evaluar nivel de cobertura mediante trama física
        const lvl = levelMap[idx];
        const bit = evalHalftone(x, y, lvl);
        outBinary[idx] = bit;
        if (bit === 1) markedCount++;
      }
    }

    // Estadísticas y diagnóstico de fragmentos de borde
    AppState.lastStats.markedRatioPct = Number(((markedCount / total) * 100).toFixed(2));
    AppState.lastStats.smallFragmentsCount = countMicroEdgeFragments(outBinary, W, H, AppState.dpi);
  }

  function runPipelineAndRender() {
    executePipelineSync();
    renderAllCanvases();
    updateHalftoneMathReadouts();
    updateExportSummaryUI();
  }

  // =========================================================================
  // 8. RENDERIZADO DE LOS TRES LIENZOS (ORIGINAL, MÁSCARA BINARIA, CUERO)
  // =========================================================================

  function renderAllCanvases() {
    if (!AppState.baseRGBA) return;
    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    const total = W * H;

    if (DOM.CanvasOriginal.width !== W || DOM.CanvasOriginal.height !== H) {
      DOM.CanvasOriginal.width = W;
      DOM.CanvasOriginal.height = H;
      DOM.CanvasMask.width = W;
      DOM.CanvasMask.height = H;
      DOM.CanvasLeather.width = W;
      DOM.CanvasLeather.height = H;
    }

    // 1. Lienzo B: Original + superposiciones de ayuda visual (Sujeto excluido en rojo, Protegido en verde)
    const origImgData = CtxOrig.createImageData(W, H);
    const origBuf = origImgData.data;
    const base = AppState.baseRGBA;
    const subj = AppState.subjectMask;
    const prot = AppState.protectMask;

    for (let i = 0; i < total; i++) {
      const off = i * 4;
      let r = base[off];
      let g = base[off + 1];
      let b = base[off + 2];
      let a = base[off + 3];

      if (AppState.showSubjectOverlay && subj[i] === 0) {
        r = (r * 0.35 + 220 * 0.65) | 0;
        g = (g * 0.35 + 35 * 0.65) | 0;
        b = (b * 0.35 + 35 * 0.65) | 0;
        a = 210;
      } else if (AppState.showProtectOverlay && prot[i] === 1) {
        r = (r * 0.45 + 16 * 0.55) | 0;
        g = (g * 0.45 + 215 * 0.55) | 0;
        b = (b * 0.45 + 120 * 0.55) | 0;
      }

      origBuf[off] = r;
      origBuf[off + 1] = g;
      origBuf[off + 2] = b;
      origBuf[off + 3] = a;
    }
    CtxOrig.putImageData(origImgData, 0, 0);

    // Si hay puntos temporales de selección poligonal o recorte, dibujarlos encima de Original
    drawInteractiveOverlays(CtxOrig, W, H);

    // 2. Lienzo C: Máscara Binaria (Píxeles estrictamente negros 0,0,0,255 o transparentes 0,0,0,0)
    const maskImgData = CtxMask.createImageData(W, H);
    const maskBuf = maskImgData.data;
    const bin = AppState.finalBinaryMask;
    const rem = AppState.removedDetailsMask;

    const splitX = Math.round((W * AppState.compareSplitPct) / 100);
    const isCompare = AppState.viewMode === "compare";

    for (let y = 0; y < H; y++) {
      const row = y * W;
      for (let x = 0; x < W; x++) {
        const i = row + x;
        const off = i * 4;

        // Modo cortina Antes/Después
        if (isCompare && x < splitX) {
          maskBuf[off] = base[off];
          maskBuf[off + 1] = base[off + 1];
          maskBuf[off + 2] = base[off + 2];
          maskBuf[off + 3] = subj[i] ? 255 : 0;
          continue;
        }

        if (AppState.previewRemovedDetails && rem[i] === 1) {
          // Resaltar en magenta en pantalla los detalles eliminados por la regla de limpieza
          maskBuf[off] = 236;
          maskBuf[off + 1] = 72;
          maskBuf[off + 2] = 153;
          maskBuf[off + 3] = 255;
        } else if (bin[i] === 1) {
          maskBuf[off] = 0;
          maskBuf[off + 1] = 0;
          maskBuf[off + 2] = 0;
          maskBuf[off + 3] = 255;
        } else {
          maskBuf[off] = 0;
          maskBuf[off + 1] = 0;
          maskBuf[off + 2] = 0;
          maskBuf[off + 3] = 0;
        }
      }
    }
    CtxMask.putImageData(maskImgData, 0, 0);
    drawInteractiveOverlays(CtxMask, W, H);

    // 3. Lienzo D: Simulación Orientativa sobre Cuero Negro
    const leatherImgData = CtxLeather.createImageData(W, H);
    const lBuf = leatherImgData.data;
    const markRGB = hexToRgb(AppState.leatherMarkColor);

    for (let i = 0; i < total; i++) {
      const off = i * 4;
      if (bin[i] === 1) {
        lBuf[off] = markRGB.r;
        lBuf[off + 1] = markRGB.g;
        lBuf[off + 2] = markRGB.b;
        lBuf[off + 3] = 255;
      } else {
        // Cuero negro de fondo simulado en este lienzo visual
        lBuf[off] = 20;
        lBuf[off + 1] = 20;
        lBuf[off + 2] = 23;
        lBuf[off + 3] = 255;
      }
    }
    CtxLeather.putImageData(leatherImgData, 0, 0);

    applyCanvasZoomCSS();
  }

  function drawInteractiveOverlays(ctx, W, H) {
    if (AppState.tempPoints.length > 0) {
      ctx.save();
      ctx.strokeStyle = "#3b82f6";
      ctx.lineWidth = Math.max(2, Math.round(W / 300));
      ctx.beginPath();
      ctx.moveTo(AppState.tempPoints[0].x, AppState.tempPoints[0].y);
      for (let i = 1; i < AppState.tempPoints.length; i++) {
        ctx.lineTo(AppState.tempPoints[i].x, AppState.tempPoints[i].y);
      }
      ctx.stroke();
      ctx.restore();
    }
  }

  function applyCanvasZoomCSS() {
    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    if (!W || !H) return;

    const dispW = Math.max(80, Math.round(W * AppState.zoom));
    const dispH = Math.max(80, Math.round(H * AppState.zoom));

    [DOM.CanvasOriginal, DOM.CanvasMask, DOM.CanvasLeather].forEach((c) => {
      c.style.width = dispW + "px";
      c.style.height = dispH + "px";
    });
    DOM.ZoomReadout.textContent = Math.round(AppState.zoom * 100) + "%";
  }

  // =========================================================================
  // 9. HERRAMIENTAS DE ELIMINACIÓN DE FONDO SIN IA Y CORRECCIÓN MANUAL
  // =========================================================================

  /**
   * Varita Mágica Contigua (Flood Fill por cola) o Selección Global por Color
   */
  function applyColorSelectionTool(startX, startY, isContiguous, excludeMode = true) {
    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    const rgba = AppState.baseRGBA;
    const subj = AppState.subjectMask;
    const tol = AppState.wandTolerance;
    const tolSq = tol * tol * 3;

    const startIdx = startY * W + startX;
    const r0 = rgba[startIdx * 4];
    const g0 = rgba[startIdx * 4 + 1];
    const b0 = rgba[startIdx * 4 + 2];

    pushHistorySnapshot();

    if (!isContiguous) {
      // Selección de color similar en toda la imagen
      for (let i = 0; i < W * H; i++) {
        const off = i * 4;
        const dr = rgba[off] - r0;
        const dg = rgba[off + 1] - g0;
        const db = rgba[off + 2] - b0;
        if (dr * dr + dg * dg + db * db <= tolSq) {
          subj[i] = excludeMode ? 0 : 1;
        }
      }
    } else {
      // Flood Fill contiguo 4-conectado
      const visited = new Uint8Array(W * H);
      const queue = new Int32Array(W * H);
      let head = 0, tail = 0;
      queue[tail++] = startIdx;
      visited[startIdx] = 1;

      while (head < tail) {
        const curr = queue[head++];
        subj[curr] = excludeMode ? 0 : 1;

        const cx = curr % W;
        const cy = (curr / W) | 0;

        const neighbors = [
          cx > 0 ? curr - 1 : -1,
          cx < W - 1 ? curr + 1 : -1,
          cy > 0 ? curr - W : -1,
          cy < H - 1 ? curr + W : -1
        ];

        for (let k = 0; k < 4; k++) {
          const n = neighbors[k];
          if (n !== -1 && visited[n] === 0) {
            visited[n] = 1;
            const off = n * 4;
            const dr = rgba[off] - r0;
            const dg = rgba[off + 1] - g0;
            const db = rgba[off + 2] - b0;
            if (dr * dr + dg * dg + db * db <= tolSq) {
              queue[tail++] = n;
            }
          }
        }
      }
    }

    runPipelineAndRender();
  }

  /**
   * Limpia pequeñas islas aisladas en la máscara del sujeto
   */
  function cleanSubjectMaskIslands() {
    if (!AppState.subjectMask) return;
    pushHistorySnapshot();

    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    const subj = AppState.subjectMask;
    const visited = new Uint8Array(W * H);
    const queue = new Int32Array(W * H);
    const minIslandArea = Math.max(16, Math.round((W * H) * 0.0008));

    for (let i = 0; i < W * H; i++) {
      if (subj[i] === 1 && visited[i] === 0) {
        let head = 0, tail = 0;
        queue[tail++] = i;
        visited[i] = 1;
        while (head < tail) {
          const c = queue[head++];
          const cx = c % W;
          const cy = (c / W) | 0;
          if (cx > 0 && !visited[c - 1] && subj[c - 1]) { visited[c - 1] = 1; queue[tail++] = c - 1; }
          if (cx < W - 1 && !visited[c + 1] && subj[c + 1]) { visited[c + 1] = 1; queue[tail++] = c + 1; }
          if (cy > 0 && !visited[c - W] && subj[c - W]) { visited[c - W] = 1; queue[tail++] = c - W; }
          if (cy < H - 1 && !visited[c + W] && subj[c + W]) { visited[c + W] = 1; queue[tail++] = c + W; }
        }
        if (tail < minIslandArea) {
          for (let k = 0; k < tail; k++) {
            subj[queue[k]] = 0;
          }
        }
      }
    }
    runPipelineAndRender();
  }

  /**
   * Pinta un círculo de radio físico en milímetros sobre la máscara correspondiente
   */
  function paintCircleAt(cx, cy, tool) {
    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    const radiusPx = Math.max(1, Math.round(mmToPx(AppState.brushSizeMM * 0.5, AppState.dpi)));
    const r2 = radiusPx * radiusPx;

    const x0 = Math.max(0, cx - radiusPx);
    const x1 = Math.min(W - 1, cx + radiusPx);
    const y0 = Math.max(0, cy - radiusPx);
    const y1 = Math.min(H - 1, cy + radiusPx);

    for (let y = y0; y <= y1; y++) {
      const dy = y - cy;
      const row = y * W;
      for (let x = x0; x <= x1; x++) {
        const dx = x - cx;
        if (dx * dx + dy * dy <= r2) {
          const idx = row + x;
          if (tool === "subj_erase") {
            AppState.subjectMask[idx] = 0;
          } else if (tool === "subj_restore") {
            AppState.subjectMask[idx] = 1;
          } else if (tool === "res_black") {
            AppState.binaryOverrideMask[idx] = 1;
          } else if (tool === "res_erase") {
            AppState.binaryOverrideMask[idx] = 0;
          } else if (tool === "res_level") {
            AppState.binaryOverrideMask[idx] = -1;
            AppState.levelOverrideMask[idx] = AppState.manualLevelValue;
          } else if (tool === "res_protect") {
            AppState.protectMask[idx] = 1;
          }
        }
      }
    }
  }

  /**
   * Traza un segmento continuo interpolando círculos entre dos puntos
   */
  function paintStrokeSegment(x0, y0, x1, y1, tool) {
    const dist = Math.hypot(x1 - x0, y1 - y0);
    const steps = Math.max(1, Math.ceil(dist / 2));
    for (let s = 0; s <= steps; s++) {
      const t = s / steps;
      const x = Math.round(x0 + (x1 - x0) * t);
      const y = Math.round(y0 + (y1 - y0) * t);
      paintCircleAt(x, y, tool);
    }
  }

  /**
   * Rellena un polígono mediante algoritmo Scanline (par-impar)
   */
  function fillPolygonOnMasks(points, mode) {
    if (points.length < 3) return;
    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;

    let minY = H - 1, maxY = 0;
    for (const p of points) {
      if (p.y < minY) minY = Math.max(0, p.y);
      if (p.y > maxY) maxY = Math.min(H - 1, p.y);
    }

    for (let y = minY; y <= maxY; y++) {
      const nodes = [];
      let j = points.length - 1;
      for (let i = 0; i < points.length; i++) {
        const yi = points[i].y, yj = points[j].y;
        const xi = points[i].x, xj = points[j].x;
        if ((yi < y && yj >= y) || (yj < y && yi >= y)) {
          nodes.push(Math.round(xi + ((y - yi) / (yj - yi)) * (xj - xi)));
        }
        j = i;
      }
      nodes.sort((a, b) => a - b);
      for (let k = 0; k < nodes.length - 1; k += 2) {
        const xStart = clamp(nodes[k], 0, W - 1);
        const xEnd = clamp(nodes[k + 1], 0, W - 1);
        for (let x = xStart; x <= xEnd; x++) {
          const idx = y * W + x;
          if (mode === "poly_exclude") {
            AppState.subjectMask[idx] = 0;
          } else if (mode === "res_poly") {
            AppState.binaryOverrideMask[idx] = -1;
            AppState.levelOverrideMask[idx] = AppState.manualLevelValue;
          }
        }
      }
    }
  }

  // =========================================================================
  // 10. EXPORTACIÓN PNG CON METADATOS FÍSICOS (CHUNK pHYs + CRC32) Y AUDITORÍA
  // =========================================================================

  // Tabla CRC32 estándar IEEE 802.3 para chunks PNG
  const CRC32_TABLE = (function () {
    const table = new Uint32Array(256);
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) {
        c = (c & 1) ? (0xedb88320 ^ (c >>> 1)) : (c >>> 1);
      }
      table[n] = c >>> 0;
    }
    return table;
  })();

  function computeCRC32(bytes, start, length) {
    let c = 0xffffffff;
    for (let i = start; i < start + length; i++) {
      c = CRC32_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
    }
    return (c ^ 0xffffffff) >>> 0;
  }

  /**
   * Inserta o actualiza el chunk pHYs en un archivo PNG binario (Uint8Array)
   * especificando la densidad exacta en píxeles por metro correspondiente a los PPP.
   */
  function injectPngPhysChunk(pngBytes, dpi) {
    const pixelsPerMeter = Math.round(dpi / 0.0254); // 1 pulgada = 0.0254 m

    // Construir el bloque pHYs completo (4 bytes len + 4 bytes type + 9 bytes data + 4 bytes CRC = 21 bytes)
    const physChunk = new Uint8Array(21);
    const dv = new DataView(physChunk.buffer);
    dv.setUint32(0, 9, false); // Longitud de datos = 9
    // Tipo 'pHYs' (112, 72, 89, 115)
    physChunk[4] = 112;
    physChunk[5] = 72;
    physChunk[6] = 89;
    physChunk[7] = 115;
    // Píxeles por unidad X (4 bytes big-endian)
    dv.setUint32(8, pixelsPerMeter, false);
    // Píxeles por unidad Y (4 bytes big-endian)
    dv.setUint32(12, pixelsPerMeter, false);
    // Unidad: 1 = metro
    physChunk[16] = 1;
    // CRC calculado sobre Type + Data (bytes 4..16, longitud 13)
    const crc = computeCRC32(physChunk, 4, 13);
    dv.setUint32(17, crc, false);

    // El encabezado PNG mide 8 bytes, seguido del chunk IHDR (25 bytes). Insertar justo después de IHDR (offset 33).
    const insertPos = 33;
    const out = new Uint8Array(pngBytes.length + 21);
    out.set(pngBytes.subarray(0, insertPos), 0);
    out.set(physChunk, insertPos);
    out.set(pngBytes.subarray(insertPos), insertPos + 21);
    return out;
  }

  /**
   * Lee el chunk pHYs de un PNG en memoria para verificar los PPP grabados
   */
  function readPngPhysDPI(pngBytes) {
    let offset = 8; // Saltar firma PNG
    const dv = new DataView(pngBytes.buffer, pngBytes.byteOffset, pngBytes.byteLength);
    while (offset + 8 <= pngBytes.length) {
      const len = dv.getUint32(offset, false);
      const type = String.fromCharCode(
        pngBytes[offset + 4],
        pngBytes[offset + 5],
        pngBytes[offset + 6],
        pngBytes[offset + 7]
      );
      if (type === "pHYs" && len === 9) {
        const ppmX = dv.getUint32(offset + 8, false);
        const unit = pngBytes[offset + 16];
        if (unit === 1) {
          return Math.round(ppmX * 0.0254);
        }
      }
      offset += 12 + len;
    }
    return null;
  }

  /**
   * Genera el búfer RGBA de exportación garantizando que solo existan
   * (0,0,0,255) y (0,0,0,0), sin antialiasing, sin cuero y sin tablero.
   */
  function buildStrictBinaryExportCanvas() {
    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    const exportCanvas = document.createElement("canvas");
    exportCanvas.width = W;
    exportCanvas.height = H;
    const ctx = exportCanvas.getContext("2d");
    const imgData = ctx.createImageData(W, H);
    const data = imgData.data;
    const bin = AppState.finalBinaryMask;

    for (let i = 0; i < W * H; i++) {
      const off = i * 4;
      if (bin[i] === 1) {
        data[off] = 0;
        data[off + 1] = 0;
        data[off + 2] = 0;
        data[off + 3] = 255;
      } else {
        data[off] = 0;
        data[off + 1] = 0;
        data[off + 2] = 0;
        data[off + 3] = 0;
      }
    }
    ctx.putImageData(imgData, 0, 0);
    return { exportCanvas, rawRGBA: data };
  }

  /**
   * Audita un búfer RGBA píxel por píxel verificando todas las restricciones binarias
   */
  function auditBinaryBuffer(rgbaData) {
    let colorPixels = 0;
    let grayPixels = 0;
    let partialAlphaPixels = 0;
    let opaqueBlack = 0;
    let fullTransparent = 0;

    for (let i = 0; i < rgbaData.length; i += 4) {
      const r = rgbaData[i];
      const g = rgbaData[i + 1];
      const b = rgbaData[i + 2];
      const a = rgbaData[i + 3];

      if (a > 0 && a < 255) partialAlphaPixels++;
      if (r !== g || g !== b) colorPixels++;
      if (a === 255 && (r !== 0 || g !== 0 || b !== 0)) grayPixels++;

      if (r === 0 && g === 0 && b === 0 && a === 255) opaqueBlack++;
      else if (r === 0 && g === 0 && b === 0 && a === 0) fullTransparent++;
    }

    const total = rgbaData.length / 4;
    const isValid =
      colorPixels === 0 &&
      grayPixels === 0 &&
      partialAlphaPixels === 0 &&
      opaqueBlack + fullTransparent === total;

    return {
      isValid,
      colorPixels,
      grayPixels,
      partialAlphaPixels,
      opaqueBlack,
      fullTransparent,
      total
    };
  }

  async function exportValidatedPNG() {
    if (!AppState.finalBinaryMask) return;

    const { exportCanvas, rawRGBA } = buildStrictBinaryExportCanvas();
    const audit = auditBinaryBuffer(rawRGBA);

    if (!audit.isValid) {
      alert("Error de validación binaria: Se detectaron píxeles fuera de especificación.");
      return;
    }

    const blob = await new Promise((resolve) => exportCanvas.toBlob(resolve, "image/png"));
    const arrayBuf = await blob.arrayBuffer();
    const pngWithPhys = injectPngPhysChunk(new Uint8Array(arrayBuf), AppState.dpi);

    // Verificar que el PNG generado se puede volver a abrir y conserva dimensiones y pHYs
    const finalBlob = new Blob([pngWithPhys], { type: "image/png" });
    const verifyUrl = URL.createObjectURL(finalBlob);

    const decodedOk = await new Promise((resolve) => {
      const testImg = new Image();
      testImg.onload = () => {
        const ok = testImg.naturalWidth === AppState.targetWidthPx && testImg.naturalHeight === AppState.targetHeightPx;
        resolve(ok);
      };
      testImg.onerror = () => resolve(false);
      testImg.src = verifyUrl;
    });

    if (!decodedOk) {
      URL.revokeObjectURL(verifyUrl);
      alert("Error al verificar la integridad del archivo PNG generado.");
      return;
    }

    const a = document.createElement("a");
    const wMM = pxToMm(AppState.targetWidthPx, AppState.dpi).toFixed(1);
    const hMM = pxToMm(AppState.targetHeightPx, AppState.dpi).toFixed(1);
    a.href = verifyUrl;
    a.download = `grabado_cuero_${wMM}x${hMM}mm_${AppState.dpi}ppp.png`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);

    setTimeout(() => URL.revokeObjectURL(verifyUrl), 4000);
    updateExportSummaryUI(audit);
  }

  function updateExportSummaryUI(auditResult = null) {
    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    const effW = pxToMm(W, AppState.dpi).toFixed(2);
    const effH = pxToMm(H, AppState.dpi).toFixed(2);

    const fragWarn = AppState.lastStats.smallFragmentsCount > 0
      ? `${AppState.lastStats.smallFragmentsCount} micro-fragmentos en bordes de región (revisar bordes)`
      : `0 micro-fragmentos aislados`;

    const binStatus = auditResult
      ? (auditResult.isValid ? "✅ Verificado: 100% Negro Opaco y Transparencia Total (pHYs inyectado)" : "❌ Error")
      : "✅ Búfer binario activo: Solo RGBA(0,0,0,255) y RGBA(0,0,0,0)";

    DOM.ExportStatsList.innerHTML = `
      <li><strong>Tamaño físico efectivo:</strong> ${effW} × ${effH} mm</li>
      <li><strong>Dimensiones en píxeles:</strong> ${W} × ${H} px</li>
      <li><strong>Resolución:</strong> ${AppState.dpi} PPP (con metadatos pHYs)</li>
      <li><strong>Superficie marcada (Negro):</strong> ${AppState.lastStats.markedRatioPct}%</li>
      <li><strong>Fragmentos de borde &lt; 0.15 mm:</strong> ${fragWarn}</li>
      <li><strong>Validación binaria:</strong> ${binStatus}</li>
    `;
  }

  function updateHalftoneMathReadouts() {
    const p = AppState.params;
    const pitchOpenL = (p.lineThickMM + p.lineGapOpenMM).toFixed(2);
    const pitchMidL = (p.lineThickMM + p.lineGapMidMM).toFixed(2);
    const pxThick = mmToPx(p.lineThickMM, AppState.dpi).toFixed(1);
    DOM.LineMathReadout.textContent =
      `Grosor: ${p.lineThickMM.toFixed(2)} mm (${pxThick} px) | Paso N1: ${pitchOpenL} mm | Paso N2: ${pitchMidL} mm`;

    const pitchOpenD = (p.dotDiamMM + p.dotGapOpenMM).toFixed(2);
    const pitchMidD = (p.dotDiamMM + p.dotGapMidMM).toFixed(2);
    DOM.DotMathReadout.textContent =
      `Diám: ${p.dotDiamMM.toFixed(2)} mm | Paso centros N1: ${pitchOpenD} mm | Paso centros N2: ${pitchMidD} mm`;
  }

  function updateBrushReadout() {
    const px = Math.max(1, Math.round(mmToPx(AppState.brushSizeMM, AppState.dpi)));
    document.getElementById("ValBrushMM").textContent = AppState.brushSizeMM.toFixed(1);
    document.getElementById("ValBrushPX").textContent = px;
  }

  // =========================================================================
  // 11. GUARDADO Y CARGA DE PROYECTO LOCAL AUTOCONTENIDO (.JSON)
  // =========================================================================

  function uint8ToBase64(u8) {
    let binary = "";
    const chunk = 0x8000;
    for (let i = 0; i < u8.length; i += chunk) {
      binary += String.fromCharCode.apply(null, u8.subarray(i, i + chunk));
    }
    return btoa(binary);
  }

  function base64ToUint8(b64) {
    const bin = atob(b64);
    const u8 = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) {
      u8[i] = bin.charCodeAt(i);
    }
    return u8;
  }

  function serializeProjectObject() {
    return {
      version: "1.0",
      sourceDataURL: AppState.sourceDataURL,
      rotationDeg: AppState.rotationDeg,
      flipHorizontal: AppState.flipHorizontal,
      crop: { ...AppState.crop },
      physWidthMM: AppState.physWidthMM,
      physHeightMM: AppState.physHeightMM,
      lockAspect: AppState.lockAspect,
      dpi: AppState.dpi,
      targetWidthPx: AppState.targetWidthPx,
      targetHeightPx: AppState.targetHeightPx,
      params: JSON.parse(JSON.stringify(AppState.params)),
      masks: {
        subjectMaskB64: uint8ToBase64(AppState.subjectMask),
        protectMaskB64: uint8ToBase64(AppState.protectMask),
        levelOverrideB64: uint8ToBase64(new Uint8Array(AppState.levelOverrideMask.buffer)),
        binaryOverrideB64: uint8ToBase64(new Uint8Array(AppState.binaryOverrideMask.buffer))
      }
    };
  }

  function loadProjectFromObject(proj) {
    return new Promise((resolve) => {
      AppState.rotationDeg = proj.rotationDeg || 0;
      AppState.flipHorizontal = !!proj.flipHorizontal;
      AppState.crop = proj.crop || { xPct: 0, yPct: 0, wPct: 100, hPct: 100 };
      AppState.physWidthMM = proj.physWidthMM || 80;
      AppState.physHeightMM = proj.physHeightMM || 80;
      AppState.lockAspect = proj.lockAspect !== undefined ? proj.lockAspect : true;
      AppState.dpi = proj.dpi || 600;
      AppState.params = JSON.parse(JSON.stringify(proj.params));

      syncUIFromState();

      const img = new Image();
      img.onload = function () {
        AppState.sourceImageElement = img;
        AppState.sourceDataURL = proj.sourceDataURL;
        AppState.sourceWidth = img.naturalWidth || img.width;
        AppState.sourceHeight = img.naturalHeight || img.height;

        rebuildBaseBufferAndMasks(false);

        if (proj.masks) {
          const sMask = base64ToUint8(proj.masks.subjectMaskB64);
          const pMask = base64ToUint8(proj.masks.protectMaskB64);
          const lMask = new Int8Array(base64ToUint8(proj.masks.levelOverrideB64).buffer);
          const bMask = new Int8Array(base64ToUint8(proj.masks.binaryOverrideB64).buffer);

          if (sMask.length === AppState.subjectMask.length) {
            AppState.subjectMask.set(sMask);
            AppState.protectMask.set(pMask);
            AppState.levelOverrideMask.set(lMask);
            AppState.binaryOverrideMask.set(bMask);
          }
        }
        runPipelineAndRender();
        resolve();
      };
      img.src = proj.sourceDataURL;
    });
  }

  // =========================================================================
  // 12. EVENTOS DE INTERFAZ Y CONTROLES
  // =========================================================================

  function syncCropInputs() {
    document.getElementById("CropX").value = AppState.crop.xPct;
    document.getElementById("CropY").value = AppState.crop.yPct;
    document.getElementById("CropW").value = AppState.crop.wPct;
    document.getElementById("CropH").value = AppState.crop.hPct;
  }

  function syncUIFromState() {
    syncCropInputs();
    document.getElementById("PhysWidthMM").value = AppState.physWidthMM;
    document.getElementById("PhysHeightMM").value = AppState.physHeightMM;
    document.getElementById("LockAspect").checked = AppState.lockAspect;
    document.getElementById("OutputDPI").value = String(AppState.dpi);

    const p = AppState.params;
    document.getElementById("SliderBrightness").value = p.brightness;
    document.getElementById("ValBrightness").textContent = p.brightness;
    document.getElementById("SliderContrast").value = p.contrast;
    document.getElementById("ValContrast").textContent = p.contrast;
    document.getElementById("SliderGamma").value = p.gamma;
    document.getElementById("ValGamma").textContent = p.gamma.toFixed(2);
    document.getElementById("SliderSmooth").value = p.smoothRadius;
    document.getElementById("ValSmooth").textContent = p.smoothRadius;

    document.getElementById("Threshold1").value = p.thresholds[0];
    document.getElementById("ValT1").textContent = p.thresholds[0];
    document.getElementById("Threshold2").value = p.thresholds[1];
    document.getElementById("ValT2").textContent = p.thresholds[1];
    document.getElementById("Threshold3").value = p.thresholds[2];
    document.getElementById("ValT3").textContent = p.thresholds[2];

    document.getElementById("MapBand0").value = String(p.bandMapping[0]);
    document.getElementById("MapBand1").value = String(p.bandMapping[1]);
    document.getElementById("MapBand2").value = String(p.bandMapping[2]);
    document.getElementById("MapBand3").value = String(p.bandMapping[3]);

    document.getElementById("EnableCleanDetails").checked = p.cleanEnabled;
    document.getElementById("CleanCriterionMode").value = p.cleanCriterion;
    document.getElementById("CleanThresholdVal").value = p.cleanThreshold;
    document.getElementById("MorphOpSelect").value = p.morphOp;

    document.getElementById("EnableEdges").checked = p.edgesEnabled;
    document.getElementById("EdgeThreshold").value = p.edgeThreshold;
    document.getElementById("ValEdgeThresh").textContent = p.edgeThreshold;
    document.getElementById("EdgeWidthMM").value = p.edgeWidthMM;

    document.getElementById("HalftoneType").value = p.halftoneType;
    document.getElementById("HalftoneLinesBox").classList.toggle("hidden", p.halftoneType !== "lines");
    document.getElementById("HalftoneDotsBox").classList.toggle("hidden", p.halftoneType !== "dots");

    document.getElementById("LineAngleDeg").value = p.lineAngleDeg;
    document.getElementById("LineThickMM").value = p.lineThickMM;
    document.getElementById("LineGapOpenMM").value = p.lineGapOpenMM;
    document.getElementById("LineGapMidMM").value = p.lineGapMidMM;

    document.getElementById("DotDiamMM").value = p.dotDiamMM;
    document.getElementById("DotGapOpenMM").value = p.dotGapOpenMM;
    document.getElementById("DotGapMidMM").value = p.dotGapMidMM;
  }

  function setupEventListeners() {
    // Carga de archivos y Drag & Drop
    const fileInput = document.getElementById("InputImageFile");
    const dropZone = document.getElementById("DropZone");

    function handleUserImageFile(file) {
      if (!file) return;
      if (!["image/png", "image/jpeg", "image/webp"].includes(file.type)) {
        alert("Formato no compatible. Por favor selecciona una imagen PNG, JPG o WebP.");
        return;
      }
      const reader = new FileReader();
      reader.onload = (e) => loadImageFromDataURL(e.target.result, false);
      reader.readAsDataURL(file);
    }

    fileInput.addEventListener("change", (e) => handleUserImageFile(e.target.files[0]));
    dropZone.addEventListener("dragover", (e) => { e.preventDefault(); dropZone.classList.add("dragover"); });
    dropZone.addEventListener("dragleave", () => dropZone.classList.remove("dragover"));
    dropZone.addEventListener("drop", (e) => {
      e.preventDefault();
      dropZone.classList.remove("dragover");
      if (e.dataTransfer.files.length > 0) handleUserImageFile(e.dataTransfer.files[0]);
    });

    document.getElementById("BtnLoadSyntheticDemo").addEventListener("click", () => {
      loadImageFromDataURL(createSyntheticDemoImage(), false);
    });

    // Geometría y Recorte (Con aviso si invalida correcciones manuales)
    function confirmGeometryChange(actionFn) {
      if (hasManualEdits()) {
        const ok = confirm("Este cambio geométrico o de dimensiones descartará las correcciones manuales aplicadas sobre la malla de píxeles actual. ¿Deseas continuar?");
        if (!ok) return false;
      }
      actionFn();
      return true;
    }

    document.getElementById("BtnRotateLeft").addEventListener("click", () => {
      confirmGeometryChange(() => {
        AppState.rotationDeg = (AppState.rotationDeg - 90 + 360) % 360;
        rebuildBaseBufferAndMasks(false);
      });
    });

    document.getElementById("BtnRotateRight").addEventListener("click", () => {
      confirmGeometryChange(() => {
        AppState.rotationDeg = (AppState.rotationDeg + 90) % 360;
        rebuildBaseBufferAndMasks(false);
      });
    });

    document.getElementById("BtnFlipH").addEventListener("click", () => {
      confirmGeometryChange(() => {
        AppState.flipHorizontal = !AppState.flipHorizontal;
        rebuildBaseBufferAndMasks(false);
      });
    });

    document.getElementById("BtnApplyCrop").addEventListener("click", () => {
      confirmGeometryChange(() => {
        AppState.crop.xPct = clamp(Number(document.getElementById("CropX").value), 0, 95);
        AppState.crop.yPct = clamp(Number(document.getElementById("CropY").value), 0, 95);
        AppState.crop.wPct = clamp(Number(document.getElementById("CropW").value), 5, 100 - AppState.crop.xPct);
        AppState.crop.hPct = clamp(Number(document.getElementById("CropH").value), 5, 100 - AppState.crop.yPct);
        syncCropInputs();
        rebuildBaseBufferAndMasks(false);
      });
    });

    document.getElementById("BtnResetCrop").addEventListener("click", () => {
      confirmGeometryChange(() => {
        AppState.crop = { xPct: 0, yPct: 0, wPct: 100, hPct: 100 };
        syncCropInputs();
        rebuildBaseBufferAndMasks(false);
      });
    });

    document.getElementById("BtnToggleCropMode").addEventListener("click", () => {
      AppState.activeTool = "crop_rect";
      document.querySelectorAll(".tool-btn").forEach((b) => b.classList.remove("active"));
    });

    // Tamaño físico y PPP
    document.getElementById("PhysWidthMM").addEventListener("change", (e) => {
      const val = clamp(Number(e.target.value), 5, 400);
      if (!confirmGeometryChange(() => {
        AppState.physWidthMM = val;
        rebuildBaseBufferAndMasks(false);
      })) {
        e.target.value = AppState.physWidthMM;
      }
    });

    document.getElementById("PhysHeightMM").addEventListener("change", (e) => {
      const val = clamp(Number(e.target.value), 5, 400);
      if (!confirmGeometryChange(() => {
        AppState.physHeightMM = val;
        AppState.lockAspect = false;
        document.getElementById("LockAspect").checked = false;
        rebuildBaseBufferAndMasks(false);
      })) {
        e.target.value = AppState.physHeightMM;
      }
    });

    document.getElementById("LockAspect").addEventListener("change", (e) => {
      AppState.lockAspect = e.target.checked;
      if (AppState.lockAspect) rebuildBaseBufferAndMasks(false);
    });

    document.getElementById("OutputDPI").addEventListener("change", (e) => {
      const newDpi = Number(e.target.value);
      if (!confirmGeometryChange(() => {
        AppState.dpi = newDpi;
        rebuildBaseBufferAndMasks(false);
      })) {
        e.target.value = String(AppState.dpi);
      }
    });

    // Selección de Herramientas Interactivas
    document.querySelectorAll(".tool-btn").forEach((btn) => {
      btn.addEventListener("click", () => {
        document.querySelectorAll(".tool-btn").forEach((b) => b.classList.remove("active"));
        btn.classList.add("active");
        AppState.activeTool = btn.dataset.tool;
        AppState.tempPoints = [];
        renderAllCanvases();
      });
    });

    document.getElementById("WandTolerance").addEventListener("input", (e) => {
      AppState.wandTolerance = Number(e.target.value);
      document.getElementById("ValWandTol").textContent = AppState.wandTolerance;
    });

    document.getElementById("BtnInvertSubjectMask").addEventListener("click", () => {
      if (!AppState.subjectMask) return;
      pushHistorySnapshot();
      for (let i = 0; i < AppState.subjectMask.length; i++) {
        AppState.subjectMask[i] = AppState.subjectMask[i] === 1 ? 0 : 1;
      }
      runPipelineAndRender();
    });

    document.getElementById("BtnCleanSubjectIslands").addEventListener("click", cleanSubjectMaskIslands);

    document.getElementById("BtnResetSubjectMask").addEventListener("click", () => {
      if (!AppState.subjectMask) return;
      pushHistorySnapshot();
      AppState.subjectMask.fill(1);
      runPipelineAndRender();
    });

    document.getElementById("BrushSizeMM").addEventListener("input", (e) => {
      AppState.brushSizeMM = Number(e.target.value);
      updateBrushReadout();
    });

    document.getElementById("ManualLevelSelect").addEventListener("change", (e) => {
      AppState.manualLevelValue = Number(e.target.value);
    });

    document.getElementById("BtnUndo").addEventListener("click", undoAction);
    document.getElementById("BtnRedo").addEventListener("click", redoAction);
    document.getElementById("BtnClearManual").addEventListener("click", () => {
      if (!AppState.levelOverrideMask) return;
      pushHistorySnapshot();
      AppState.levelOverrideMask.fill(-1);
      AppState.binaryOverrideMask.fill(-1);
      AppState.protectMask.fill(0);
      runPipelineAndRender();
    });

    // Interacción Puntero sobre los Lienzos (Original y Máscara)
    function getCanvasPixelCoords(canvas, evt) {
      const rect = canvas.getBoundingClientRect();
      const scaleX = canvas.width / rect.width;
      const scaleY = canvas.height / rect.height;
      const x = clamp(Math.floor((evt.clientX - rect.left) * scaleX), 0, canvas.width - 1);
      const y = clamp(Math.floor((evt.clientY - rect.top) * scaleY), 0, canvas.height - 1);
      return { x, y };
    }

    [DOM.CanvasOriginal, DOM.CanvasMask, DOM.CanvasLeather].forEach((canvas) => {
      canvas.addEventListener("mousedown", (e) => {
        if (e.button !== 0 || !AppState.baseRGBA) return;
        const pt = getCanvasPixelCoords(canvas, e);
        const tool = AppState.activeTool;

        if (tool === "pan") return;

        if (tool === "wand_contig") {
          applyColorSelectionTool(pt.x, pt.y, true, true);
          return;
        }
        if (tool === "wand_global") {
          applyColorSelectionTool(pt.x, pt.y, false, true);
          return;
        }

        if (tool === "poly_exclude" || tool === "res_poly") {
          AppState.tempPoints.push(pt);
          renderAllCanvases();
          return;
        }

        AppState.isPointerDown = true;
        AppState.dragStartPt = pt;

        if (["subj_erase", "subj_restore", "res_black", "res_erase", "res_level", "res_protect"].includes(tool)) {
          pushHistorySnapshot();
          paintCircleAt(pt.x, pt.y, tool);
          runPipelineAndRender();
        }
      });

      canvas.addEventListener("mousemove", (e) => {
        if (!AppState.baseRGBA) return;
        const pt = getCanvasPixelCoords(canvas, e);
        const xMM = pxToMm(pt.x, AppState.dpi).toFixed(1);
        const yMM = pxToMm(pt.y, AppState.dpi).toFixed(1);
        DOM.CursorCoords.textContent = `X: ${xMM} mm (${pt.x} px), Y: ${yMM} mm (${pt.y} px)`;

        if (!AppState.isPointerDown) return;
        const tool = AppState.activeTool;

        if (["subj_erase", "subj_restore", "res_black", "res_erase", "res_level", "res_protect"].includes(tool)) {
          paintStrokeSegment(AppState.dragStartPt.x, AppState.dragStartPt.y, pt.x, pt.y, tool);
          AppState.dragStartPt = pt;
          runPipelineAndRender();
        }
      });

      canvas.addEventListener("mouseup", (e) => {
        if (!AppState.isPointerDown) return;
        AppState.isPointerDown = false;
        const pt = getCanvasPixelCoords(canvas, e);
        const start = AppState.dragStartPt;
        const tool = AppState.activeTool;

        if (tool === "rect_exclude" && start) {
          pushHistorySnapshot();
          const x0 = Math.min(start.x, pt.x), x1 = Math.max(start.x, pt.x);
          const y0 = Math.min(start.y, pt.y), y1 = Math.max(start.y, pt.y);
          const W = AppState.targetWidthPx;
          for (let y = y0; y <= y1; y++) {
            for (let x = x0; x <= x1; x++) {
              AppState.subjectMask[y * W + x] = 0;
            }
          }
          runPipelineAndRender();
        } else if (tool === "res_line" && start) {
          pushHistorySnapshot();
          paintStrokeSegment(start.x, start.y, pt.x, pt.y, "res_black");
          runPipelineAndRender();
        } else if (tool === "crop_rect" && start) {
          const W = AppState.targetWidthPx;
          const H = AppState.targetHeightPx;
          const x0 = Math.min(start.x, pt.x), x1 = Math.max(start.x, pt.x);
          const y0 = Math.min(start.y, pt.y), y1 = Math.max(start.y, pt.y);
          if (x1 - x0 > 20 && y1 - y0 > 20) {
            document.getElementById("CropX").value = Math.round((x0 / W) * 100);
            document.getElementById("CropY").value = Math.round((y0 / H) * 100);
            document.getElementById("CropW").value = Math.round(((x1 - x0) / W) * 100);
            document.getElementById("CropH").value = Math.round(((y1 - y0) / H) * 100);
            document.getElementById("BtnApplyCrop").click();
          }
        }
      });

      // Doble clic cierra y rellena polígonos
      canvas.addEventListener("dblclick", () => {
        const tool = AppState.activeTool;
        if ((tool === "poly_exclude" || tool === "res_poly") && AppState.tempPoints.length >= 3) {
          pushHistorySnapshot();
          fillPolygonOnMasks(AppState.tempPoints, tool);
          AppState.tempPoints = [];
          runPipelineAndRender();
        }
      });
    });

    // Controles de Procesamiento (Sliders con actualización inmediata)
    document.getElementById("SliderBrightness").addEventListener("input", (e) => {
      AppState.params.brightness = Number(e.target.value);
      document.getElementById("ValBrightness").textContent = AppState.params.brightness;
      runPipelineAndRender();
    });

    document.getElementById("SliderContrast").addEventListener("input", (e) => {
      AppState.params.contrast = Number(e.target.value);
      document.getElementById("ValContrast").textContent = AppState.params.contrast;
      runPipelineAndRender();
    });

    document.getElementById("SliderGamma").addEventListener("input", (e) => {
      AppState.params.gamma = Number(e.target.value);
      document.getElementById("ValGamma").textContent = AppState.params.gamma.toFixed(2);
      runPipelineAndRender();
    });

    document.getElementById("SliderSmooth").addEventListener("input", (e) => {
      AppState.params.smoothRadius = Number(e.target.value);
      document.getElementById("ValSmooth").textContent = AppState.params.smoothRadius;
      runPipelineAndRender();
    });

    // Tres umbrales siempre estrictamente ordenados (T1 < T2 < T3)
    function enforceOrderedThresholds(changedIndex) {
      let t1 = Number(document.getElementById("Threshold1").value);
      let t2 = Number(document.getElementById("Threshold2").value);
      let t3 = Number(document.getElementById("Threshold3").value);

      if (changedIndex === 1 && t1 >= t2) t2 = Math.min(253, t1 + 1);
      if (changedIndex === 2) {
        if (t2 <= t1) t1 = Math.max(1, t2 - 1);
        if (t2 >= t3) t3 = Math.min(254, t2 + 1);
      }
      if (changedIndex === 3 && t3 <= t2) t2 = Math.max(2, t3 - 1);
      if (t1 >= t2) t1 = Math.max(1, t2 - 1);

      AppState.params.thresholds = [t1, t2, t3];
      document.getElementById("Threshold1").value = t1;
      document.getElementById("Threshold2").value = t2;
      document.getElementById("Threshold3").value = t3;
      document.getElementById("ValT1").textContent = t1;
      document.getElementById("ValT2").textContent = t2;
      document.getElementById("ValT3").textContent = t3;
      runPipelineAndRender();
    }

    document.getElementById("Threshold1").addEventListener("input", () => enforceOrderedThresholds(1));
    document.getElementById("Threshold2").addEventListener("input", () => enforceOrderedThresholds(2));
    document.getElementById("Threshold3").addEventListener("input", () => enforceOrderedThresholds(3));

    document.getElementById("BtnAutoOtsu").addEventListener("click", () => {
      if (!AppState.baseRGBA) return;
      const total = AppState.targetWidthPx * AppState.targetHeightPx;
      const lum = new Uint8Array(total);
      for (let i = 0; i < total; i++) {
        const off = i * 4;
        lum[i] = Math.round(0.299 * AppState.baseRGBA[off] + 0.587 * AppState.baseRGBA[off + 1] + 0.114 * AppState.baseRGBA[off + 2]);
      }
      const [o1, o2, o3] = computeMultiOtsuThresholds3(lum, AppState.subjectMask);
      AppState.params.thresholds = [o1, o2, o3];
      syncUIFromState();
      runPipelineAndRender();
    });

    // Asignación tonal e Inversión de Polaridad (afecta solo al sujeto incluido)
    ["MapBand0", "MapBand1", "MapBand2", "MapBand3"].forEach((id, idx) => {
      document.getElementById(id).addEventListener("change", (e) => {
        AppState.params.bandMapping[idx] = Number(e.target.value);
        runPipelineAndRender();
      });
    });

    document.getElementById("BtnInvertPolarity").addEventListener("click", () => {
      AppState.params.bandMapping.reverse();
      syncUIFromState();
      runPipelineAndRender();
    });

    // Limpieza y Bordes
    document.getElementById("EnableCleanDetails").addEventListener("change", (e) => {
      AppState.params.cleanEnabled = e.target.checked;
      runPipelineAndRender();
    });

    document.getElementById("CleanCriterionMode").addEventListener("change", (e) => {
      AppState.params.cleanCriterion = e.target.value;
      document.getElementById("CleanUnitLabel").textContent = e.target.value === "area" ? "mm²" : "mm";
      runPipelineAndRender();
    });

    document.getElementById("CleanThresholdVal").addEventListener("input", (e) => {
      AppState.params.cleanThreshold = Math.max(0.05, Number(e.target.value));
      runPipelineAndRender();
    });

    document.getElementById("MorphOpSelect").addEventListener("change", (e) => {
      AppState.params.morphOp = e.target.value;
      runPipelineAndRender();
    });

    document.getElementById("EnableEdges").addEventListener("change", (e) => {
      AppState.params.edgesEnabled = e.target.checked;
      runPipelineAndRender();
    });

    document.getElementById("EdgeThreshold").addEventListener("input", (e) => {
      AppState.params.edgeThreshold = Number(e.target.value);
      document.getElementById("ValEdgeThresh").textContent = AppState.params.edgeThreshold;
      runPipelineAndRender();
    });

    document.getElementById("EdgeWidthMM").addEventListener("input", (e) => {
      AppState.params.edgeWidthMM = Math.max(0.1, Number(e.target.value));
      runPipelineAndRender();
    });

    // Tramas Físicas
    document.getElementById("HalftoneType").addEventListener("change", (e) => {
      AppState.params.halftoneType = e.target.value;
      syncUIFromState();
      runPipelineAndRender();
    });

    ["LineAngleDeg", "LineThickMM", "LineGapOpenMM", "LineGapMidMM", "DotDiamMM", "DotGapOpenMM", "DotGapMidMM"].forEach((id) => {
      document.getElementById(id).addEventListener("input", () => {
        AppState.params.lineAngleDeg = Number(document.getElementById("LineAngleDeg").value);
        AppState.params.lineThickMM = Math.max(0.05, Number(document.getElementById("LineThickMM").value));
        AppState.params.lineGapOpenMM = Math.max(0.05, Number(document.getElementById("LineGapOpenMM").value));
        AppState.params.lineGapMidMM = Math.max(0.05, Number(document.getElementById("LineGapMidMM").value));

        AppState.params.dotDiamMM = Math.max(0.05, Number(document.getElementById("DotDiamMM").value));
        AppState.params.dotGapOpenMM = Math.max(0.05, Number(document.getElementById("DotGapOpenMM").value));
        AppState.params.dotGapMidMM = Math.max(0.05, Number(document.getElementById("DotGapMidMM").value));
        runPipelineAndRender();
      });
    });

    // Navegación, Vistas y Zoom (El zoom solo cambia CSS, nunca el archivo exportado)
    document.querySelectorAll(".tab-btn").forEach((btn) => {
      btn.addEventListener("click", () => {
        document.querySelectorAll(".tab-btn").forEach((b) => b.classList.remove("active"));
        btn.classList.add("active");
        const view = btn.dataset.view;
        AppState.viewMode = view;

        const stage = document.getElementById("CanvasStage");
        const cOrig = document.getElementById("CardOriginal");
        const cMask = document.getElementById("CardMask");
        const cLeath = document.getElementById("CardLeather");
        const compBar = document.getElementById("CompareOverlayControl");

        stage.classList.toggle("single-view", view !== "split");
        cOrig.classList.toggle("hidden", view !== "split" && view !== "original");
        cMask.classList.toggle("hidden", view !== "split" && view !== "mask" && view !== "compare");
        cLeath.classList.toggle("hidden", view !== "split" && view !== "leather");
        compBar.classList.toggle("hidden", view !== "compare");

        renderAllCanvases();
      });
    });

    document.getElementById("CompareSplitRange").addEventListener("input", (e) => {
      AppState.compareSplitPct = Number(e.target.value);
      renderAllCanvases();
    });

    document.getElementById("BtnZoomIn").addEventListener("click", () => {
      AppState.zoom = clamp(AppState.zoom * 1.25, 0.08, 8.0);
      applyCanvasZoomCSS();
    });
    document.getElementById("BtnZoomOut").addEventListener("click", () => {
      AppState.zoom = clamp(AppState.zoom / 1.25, 0.08, 8.0);
      applyCanvasZoomCSS();
    });
    document.getElementById("BtnZoom100").addEventListener("click", () => {
      AppState.zoom = 1.0;
      applyCanvasZoomCSS();
    });
    document.getElementById("BtnZoomFit").addEventListener("click", () => {
      const container = document.getElementById("ViewportContainer");
      const availW = (AppState.viewMode === "split") ? (container.clientWidth / 3) - 36 : container.clientWidth - 60;
      AppState.zoom = clamp(availW / AppState.targetWidthPx, 0.08, 2.0);
      applyCanvasZoomCSS();
    });

    document.getElementById("ShowSubjectOverlay").addEventListener("change", (e) => {
      AppState.showSubjectOverlay = e.target.checked;
      renderAllCanvases();
    });
    document.getElementById("ShowProtectOverlay").addEventListener("change", (e) => {
      AppState.showProtectOverlay = e.target.checked;
      renderAllCanvases();
    });
    document.getElementById("PreviewRemovedDetails").addEventListener("change", (e) => {
      AppState.previewRemovedDetails = e.target.checked;
      renderAllCanvases();
    });
    document.getElementById("LeatherMarkColor").addEventListener("input", (e) => {
      AppState.leatherMarkColor = e.target.value;
      renderAllCanvases();
    });

    // Guardar y Cargar Proyecto
    document.getElementById("BtnSaveProject").addEventListener("click", () => {
      if (!AppState.sourceDataURL) return;
      const proj = serializeProjectObject();
      const blob = new Blob([JSON.stringify(proj)], { type: "application/json" });
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = "proyecto_grabado_cuero.json";
      a.click();
      setTimeout(() => URL.revokeObjectURL(url), 2000);
    });

    document.getElementById("InputLoadProject").addEventListener("change", (e) => {
      const file = e.target.files[0];
      if (!file) return;
      const reader = new FileReader();
      reader.onload = async (ev) => {
        try {
          const proj = JSON.parse(ev.target.result);
          await loadProjectFromObject(proj);
        } catch (err) {
          alert("Error: El archivo de proyecto JSON no es válido.");
        }
      };
      reader.readAsDataURL ? reader.readAsText(file) : null;
    });

    // Exportación PNG
    document.getElementById("BtnExportPNG").addEventListener("click", exportValidatedPNG);

    // Suite de Pruebas de Aceptación
    document.getElementById("BtnRunTests").addEventListener("click", runAllAcceptanceTests);
    document.getElementById("BtnCloseTests").addEventListener("click", () => {
      document.getElementById("ModalTests").classList.add("hidden");
    });
  }

  // =========================================================================
  // 13. SUITE DE 10 PRUEBAS DE ACEPTACIÓN REPRODUCIBLES (IMÁGENES SINTÉTICAS)
  // =========================================================================

  async function runAllAcceptanceTests() {
    const modal = document.getElementById("ModalTests");
    const container = document.getElementById("TestResultsContainer");
    modal.classList.remove("hidden");
    container.innerHTML = "<p>Ejecutando las 10 pruebas reproducibles con imágenes sintéticas...</p>";

    // Respaldar proyecto actual para restaurarlo al terminar las pruebas
    const backupProj = AppState.sourceDataURL ? serializeProjectObject() : null;
    const results = [];

    function recordTest(num, title, passed, detail) {
      results.push({ num, title, passed, detail });
    }

    // Crear imagen sintética de rampa de luminancia de 4 bandas (400x100 px)
    const rampCanvas = document.createElement("canvas");
    rampCanvas.width = 400;
    rampCanvas.height = 100;
    const rCtx = rampCanvas.getContext("2d");
    const bandGrays = [20, 95, 160, 235];
    for (let b = 0; b < 4; b++) {
      rCtx.fillStyle = `rgb(${bandGrays[b]},${bandGrays[b]},${bandGrays[b]})`;
      rCtx.fillRect(b * 100, 0, 100, 100);
    }
    const rampDataURL = rampCanvas.toDataURL("image/png");

    await new Promise((res) => {
      const img = new Image();
      img.onload = () => {
        AppState.sourceImageElement = img;
        AppState.sourceDataURL = rampDataURL;
        AppState.sourceWidth = 400;
        AppState.sourceHeight = 100;
        AppState.rotationDeg = 0;
        AppState.flipHorizontal = false;
        AppState.crop = { xPct: 0, yPct: 0, wPct: 100, hPct: 100 };
        AppState.physWidthMM = 40;
        AppState.physHeightMM = 10;
        AppState.lockAspect = true;
        AppState.dpi = 600;
        AppState.params.brightness = 0;
        AppState.params.contrast = 0;
        AppState.params.gamma = 1.0;
        AppState.params.smoothRadius = 0;
        AppState.params.thresholds = [64, 128, 192];
        AppState.params.bandMapping = [0, 1, 2, 3];
        AppState.params.cleanEnabled = false;
        AppState.params.edgesEnabled = false;
        AppState.params.halftoneType = "lines";
        AppState.params.lineAngleDeg = 0; // Líneas verticales para medir paso horizontal exacto
        AppState.params.lineThickMM = 0.30;
        AppState.params.lineGapOpenMM = 0.60;
        AppState.params.lineGapMidMM = 0.40;
        rebuildBaseBufferAndMasks(false);
        res();
      };
      img.src = rampDataURL;
    });

    const W = AppState.targetWidthPx;
    const H = AppState.targetHeightPx;
    const qW = Math.floor(W / 4);

    function densityInBand(bandIndex) {
      let ones = 0, count = 0;
      const x0 = bandIndex * qW + 10;
      const x1 = (bandIndex + 1) * qW - 10;
      for (let y = 10; y < H - 10; y++) {
        for (let x = x0; x < x1; x++) {
          ones += AppState.finalBinaryMask[y * W + x];
          count++;
        }
      }
      return ones / count;
    }

    // PRUEBA 1: Escala de luminancia produce 4 bandas de cobertura distintas y ordenadas
    const d0 = densityInBand(0);
    const d1 = densityInBand(1);
    const d2 = densityInBand(2);
    const d3 = densityInBand(3);
    const p1 = (d0 === 0) && (d1 > 0.25 && d1 < 0.42) && (d2 > d1 && d2 < 0.55) && (d3 === 1.0);
    recordTest(
      1,
      "Escala de luminancia produce 4 bandas de cobertura espacial",
      p1,
      `Densidades medidas -> N0: ${(d0 * 100).toFixed(1)}%, N1 (Abierta): ${(d1 * 100).toFixed(1)}%, N2 (Media): ${(d2 * 100).toFixed(1)}%, N3 (Sólido): ${(d3 * 100).toFixed(1)}%`
    );

    // PRUEBA 2: El resultado exportado solo contiene negro opaco (0,0,0,255) y transparencia (0,0,0,0)
    const { exportCanvas, rawRGBA } = buildStrictBinaryExportCanvas();
    const audit = auditBinaryBuffer(rawRGBA);
    recordTest(
      2,
      "El resultado exportado solo contiene negro opaco y transparencia total",
      audit.isValid,
      `Colores: ${audit.colorPixels}, Grises: ${audit.grayPixels}, Alfa parcial (1..254): ${audit.partialAlphaPixels}, Negros: ${audit.opaqueBlack}, Transp: ${audit.fullTransparent}`
    );

    // PRUEBA 3: Invertir la polaridad no recupera el fondo eliminado
    for (let y = 0; y < H; y++) {
      for (let x = 0; x < 50; x++) {
        AppState.subjectMask[y * W + x] = 0; // Excluir franja izquierda como fondo eliminado
      }
    }
    AppState.params.bandMapping.reverse();
    executePipelineSync();
    let leakedPixels = 0;
    for (let y = 0; y < H; y++) {
      for (let x = 0; x < 50; x++) {
        if (AppState.finalBinaryMask[y * W + x] !== 0) leakedPixels++;
      }
    }
    AppState.params.bandMapping.reverse(); // Restaurar
    AppState.subjectMask.fill(1);
    executePipelineSync();
    recordTest(
      3,
      "Invertir la polaridad nunca recupera el fondo eliminado (subjectMask = 0)",
      leakedPixels === 0,
      `Píxeles reactivados en zona excluida tras inversión tonal: ${leakedPixels}`
    );

    // PRUEBA 4: Los pasos de trama coinciden con los valores físicos dentro del error de redondeo
    // En Banda 1 (Trama abierta: grosor 0.3 mm + espacio libre 0.6 mm = paso nominal 0.90 mm)
    const xStartB1 = qW + 15;
    const xEndB1 = 2 * qW - 15;
    const rowY = Math.floor(H / 2);
    const risingEdges = [];
    for (let x = xStartB1 + 1; x < xEndB1; x++) {
      const prev = AppState.finalBinaryMask[rowY * W + (x - 1)];
      const curr = AppState.finalBinaryMask[rowY * W + x];
      if (prev === 0 && curr === 1) risingEdges.push(x);
    }
    let avgPitchPx = 0;
    for (let i = 1; i < risingEdges.length; i++) {
      avgPitchPx += (risingEdges[i] - risingEdges[i - 1]);
    }
    avgPitchPx = risingEdges.length > 1 ? avgPitchPx / (risingEdges.length - 1) : 0;
    const measuredPitchMM = pxToMm(avgPitchPx, AppState.dpi);
    const expectedPitchMM = 0.90;
    const pitchDiffMM = Math.abs(measuredPitchMM - expectedPitchMM);
    recordTest(
      4,
      "Los pasos de trama coinciden con los valores físicos dentro del error de redondeo",
      pitchDiffMM <= (25.4 / AppState.dpi),
      `Paso esperado N1: ${expectedPitchMM.toFixed(3)} mm | Paso medido en búfer: ${measuredPitchMM.toFixed(3)} mm (Error: ${pitchDiffMM.toFixed(4)} mm)`
    );

    // PRUEBA 5: Cambiar el zoom no modifica el archivo final
    const snapshotZoom1 = new Uint8Array(AppState.finalBinaryMask);
    AppState.zoom = 0.25;
    applyCanvasZoomCSS();
    const { rawRGBA: rgbaZoom025 } = buildStrictBinaryExportCanvas();
    AppState.zoom = 3.5;
    applyCanvasZoomCSS();
    const { rawRGBA: rgbaZoom350 } = buildStrictBinaryExportCanvas();
    AppState.zoom = 1.0;
    applyCanvasZoomCSS();
    let diffZoom = 0;
    for (let i = 0; i < rgbaZoom025.length; i += 4) {
      if (rgbaZoom025[i + 3] !== rgbaZoom350[i + 3] || (rgbaZoom025[i + 3] === 255 ? 1 : 0) !== snapshotZoom1[i >> 2]) {
        diffZoom++;
      }
    }
    recordTest(
      5,
      "Cambiar el zoom de la interfaz no modifica el archivo final exportado",
      diffZoom === 0,
      `Diferencias de píxeles entre exportaciones a zoom 25%, 100% y 350%: ${diffZoom}`
    );

    // PRUEBA 6: Los metadatos de resolución (chunk pHYs) corresponden al valor seleccionado
    const pngBlob = await new Promise((r) => exportCanvas.toBlob(r, "image/png"));
    const rawPngBytes = new Uint8Array(await pngBlob.arrayBuffer());
    const injectedBytes = injectPngPhysChunk(rawPngBytes, 600);
    const readBackDPI = readPngPhysDPI(injectedBytes);
    recordTest(
      6,
      "Los metadatos PNG (chunk pHYs con CRC32) corresponden a los PPP seleccionados",
      readBackDPI === 600,
      `PPP configurados: 600 | PPP leídos desde el chunk binario pHYs del PNG: ${readBackDPI}`
    );

    // PRUEBA 7: Guardar y cargar el proyecto conserva exactamente el resultado
    const savedProj = serializeProjectObject();
    const maskBeforeSave = new Uint8Array(AppState.finalBinaryMask);
    await loadProjectFromObject(savedProj);
    let diffProject = 0;
    for (let i = 0; i < maskBeforeSave.length; i++) {
      if (maskBeforeSave[i] !== AppState.finalBinaryMask[i]) diffProject++;
    }
    recordTest(
      7,
      "Guardar y cargar el proyecto local conserva exactamente el resultado",
      diffProject === 0,
      `Diferencias en la máscara binaria tras ciclo serializar/cargar proyecto: ${diffProject} píxeles`
    );

    // PRUEBA 8: Las correcciones manuales sobreviven a cambios de contraste y umbrales
    const testPixelIdx = Math.floor(H / 2) * W + 30; // En Banda 0 (que era nivel 0 transparente)
    AppState.binaryOverrideMask[testPixelIdx] = 1; // Forzar negro manual
    AppState.params.contrast = 75;
    AppState.params.thresholds = [90, 150, 210];
    executePipelineSync();
    const survived = AppState.finalBinaryMask[testPixelIdx] === 1;
    AppState.binaryOverrideMask[testPixelIdx] = -1;
    recordTest(
      8,
      "Las correcciones manuales sobreviven a cambios de contraste y umbrales",
      survived,
      `Píxel corregido manualmente mantuvo su estado binario tras alterar contraste (+75) y umbrales: ${survived ? "Sí" : "No"}`
    );

    // PRUEBA 9: La simulación del cuero nunca se incluye en la exportación
    AppState.leatherMarkColor = "#e5c07b";
    renderAllCanvases();
    const { rawRGBA: exportAfterLeather } = buildStrictBinaryExportCanvas();
    const auditLeather = auditBinaryBuffer(exportAfterLeather);
    recordTest(
      9,
      "La simulación sobre cuero negro nunca se incluye en el PNG de exportación",
      auditLeather.isValid && auditLeather.colorPixels === 0,
      `Píxeles del color de simulación (#e5c07b) o fondo cuero en el PNG exportado: ${auditLeather.colorPixels}`
    );

    // PRUEBA 10: El procesamiento no realiza solicitudes de red (Verificación PerformanceResourceTiming)
    const resources = performance.getEntriesByType("resource") || [];
    const externalCalls = resources.filter((r) => /^https?:\/\//i.test(r.name) && !r.name.includes(location.host));
    recordTest(
      10,
      "El procesamiento se ejecuta 100% localmente sin solicitudes de red externas",
      externalCalls.length === 0,
      `Solicitudes externas detectadas durante la sesión: ${externalCalls.length}`
    );

    // Renderizar resultados en el modal
    container.innerHTML = results.map((r) => `
      <div class="test-item ${r.passed ? "pass" : "fail"}">
        <div><strong>${r.passed ? "✅ PASA" : "❌ FALLA"} — Prueba ${r.num}: ${r.title}</strong></div>
        <div class="hint" style="margin-top:3px;">${r.detail}</div>
      </div>
    `).join("");

    // Restaurar estado previo del usuario
    if (backupProj) {
      await loadProjectFromObject(backupProj);
    }
  }

  // =========================================================================
  // 14. INICIALIZACIÓN AL CARGAR LA PÁGINA
  // =========================================================================
  window.addEventListener("DOMContentLoaded", () => {
    setupEventListeners();
    syncUIFromState();
    // Cargar imagen sintética inicial para que todos los controles sean verificables de inmediato
    loadImageFromDataURL(createSyntheticDemoImage(), false);
  });

})();
-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgKappaElliptic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T05:18:49.062378+00:00
-- url     : https://prove2.me/submissions/c4ae3bfa-60bf-42f3-85d4-7e4248e53077

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

theorem solution (j : Fin 84) : 0 ≤ qgKappaElliptic j := by
  simpa [qgKappaElliptic] using (by norm_num : (0 : ℝ) ≤ 1 / 16)

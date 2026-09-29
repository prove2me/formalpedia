-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgKappa_spatial_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T05:18:47.320391+00:00
-- url     : https://prove2.me/submissions/8bed7d2a-e737-4531-8f78-2ab6052856c2

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

theorem solution {j : Fin 84} (hj : j ≠ confIndex) : 0 < qgKappa j := by
  simpa [qgKappa, hj] using (by norm_num : (0 : ℝ) < 1 / 16)

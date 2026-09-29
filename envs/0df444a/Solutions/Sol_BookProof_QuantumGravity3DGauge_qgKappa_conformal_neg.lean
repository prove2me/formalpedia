-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgKappa_conformal_neg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T05:18:48.21118+00:00
-- url     : https://prove2.me/submissions/40a4e8c4-a2c3-469f-b26c-a930d85a3420

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

theorem solution : qgKappa confIndex < 0 := by
  simpa [qgKappa] using (by norm_num : (-(1 / 24) : ℝ) < 0)

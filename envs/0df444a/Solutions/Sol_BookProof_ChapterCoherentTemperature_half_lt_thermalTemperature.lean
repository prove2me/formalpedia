-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.half_lt_thermalTemperature
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:35:12.057264+00:00
-- url     : https://prove2.me/submissions/7a2850b9-282d-4f55-a719-5ecbc17c821c

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.half_lt_thermalTemperature
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 < nbar) : 1 / 2 < thermalTemperature nbar := by

  rw [thermalTemperature]; linarith

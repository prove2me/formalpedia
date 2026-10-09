-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.thermalRatio_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:32:57.782406+00:00
-- url     : https://prove2.me/submissions/4d230bfb-96b8-49f7-af51-0054c166513e

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.thermalRatio_nonneg
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
import Theorems.Thm_BookProof_ChapterCoherentTemperature_nbar_add_one_pos
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) : 0 ≤ thermalRatio nbar := div_nonneg h (le_of_lt (nbar_add_one_pos h))

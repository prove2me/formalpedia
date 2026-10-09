-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.norm_thermalRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:33:23.912187+00:00
-- url     : https://prove2.me/submissions/acb7e72e-9e09-4a32-8539-1244b14fedf2

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.norm_thermalRatio_lt_one
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalRatio_nonneg
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalRatio_lt_one
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) : ‖thermalRatio nbar‖ < 1 := by

  rw [Real.norm_eq_abs, abs_of_nonneg (thermalRatio_nonneg h)]
  exact thermalRatio_lt_one h

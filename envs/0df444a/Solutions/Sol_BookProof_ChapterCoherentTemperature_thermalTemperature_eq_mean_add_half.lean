-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:34:32.971989+00:00
-- url     : https://prove2.me/submissions/83f16c85-1352-40e9-98d8-05ccd7da25d0

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.thermalTemperature_eq_mean_add_half
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_mean
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) :
    thermalTemperature nbar = (∑' n : ℕ, (n : ℝ) * thermalProb nbar n) + 1 / 2 := by

  rw [thermalTemperature, thermalProb_mean h]

-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.thermalProb_tsum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:33:39.441626+00:00
-- url     : https://prove2.me/submissions/32cf87ca-65cf-4463-9010-3b994b57186b

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.thermalProb_tsum_one
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
import Theorems.Thm_BookProof_ChapterCoherentTemperature_nbar_add_one_pos
import Theorems.Thm_BookProof_ChapterCoherentTemperature_norm_thermalRatio_lt_one
import Theorems.Thm_BookProof_ChapterCoherentTemperature_one_sub_thermalRatio
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) : ∑' n : ℕ, thermalProb nbar n = 1 := by

  have hr := norm_thermalRatio_lt_one h
  have hpos := nbar_add_one_pos h
  simp only [thermalProb]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr, one_sub_thermalRatio h]
  field_simp

-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.thermalProb_mean
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:33:40.455986+00:00
-- url     : https://prove2.me/submissions/6f667d6c-0e7f-4cf2-a088-a3c5deb38378

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.thermalProb_mean
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
theorem solution (h : 0 ≤ nbar) : ∑' n : ℕ, (n : ℝ) * thermalProb nbar n = nbar := by

  have hr := norm_thermalRatio_lt_one h
  have hpos := nbar_add_one_pos h
  have hkey : ∑' n : ℕ, (n : ℝ) * thermalProb nbar n
      = (1 / (nbar + 1)) * ∑' n : ℕ, (n : ℝ) * thermalRatio nbar ^ n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by simp only [thermalProb]; ring
  rw [hkey, tsum_coe_mul_geometric_of_norm_lt_one hr, one_sub_thermalRatio h, thermalRatio]
  field_simp

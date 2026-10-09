-- Prove2me | solution 1 for BookProof.ChapterCoherentTemperature.tsum_choose_two
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:34:05.796986+00:00
-- url     : https://prove2.me/submissions/23fb0b81-8738-49e4-8772-0de3a47a487e

-- Generated from ChapterCoherentTemperature.lean — solution of BookProof.ChapterCoherentTemperature.tsum_choose_two
import Mathlib
import Definitions.Def_ChapterCoherentTemperature
import Theorems.Thm_BookProof_ChapterCoherentTemperature_norm_thermalRatio_lt_one
open BookProof.ChapterCoherentTemperature



noncomputable section




variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 ≤ nbar) :
    ∑' n : ℕ, ((n + 2).choose 2 : ℝ) * thermalRatio nbar ^ n
      = 1 / (1 - thermalRatio nbar) ^ 3 := tsum_choose_mul_geometric_of_norm_lt_one 2 (norm_thermalRatio_lt_one h)

-- Prove2me | solution 1 for BookProof.ChapterLayerNorm.variance_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:26:18.003753+00:00
-- url     : https://prove2.me/submissions/dedab4af-71b5-49f1-acec-ae384797a001

-- Generated from ChapterLayerNorm.lean — solution of BookProof.ChapterLayerNorm.variance_smul
import Mathlib
import Definitions.Def_ChapterLayerNorm
import Theorems.Thm_BookProof_ChapterLayerNorm_mean_smul
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterTotalVariance
open BookProof.ChapterLayerNorm



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a : ℝ) (x : Fin d → ℝ) :
    variance (fun i => a * x i) = a ^ 2 * variance x := by

  have hsum : ∑ i, (a * x i - a * mean x) ^ 2 = a ^ 2 * ∑ i, (x i - mean x) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [variance, mean_smul]
  rw [hsum, mul_div_assoc]

-- Prove2me | solution 1 for BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:49:49.561552+00:00
-- url     : https://prove2.me/submissions/90ce7063-9319-484e-840f-747771249425

-- Generated from ChapterCrossEntropyGradient.lean — solution of BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_sum_zero
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterCrossEntropyGradient



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (y : Fin m) :
    ∑ i, crossEntropyGradient beta s y i = 0 := by

  have hsum : ∑ i, scoreSoftmax beta s i = 1 := scoreSoftmax_sum_one beta s y
  have hdelta : ∑ i : Fin m, (if i = y then (1 : ℝ) else 0) = 1 := by
    simp
  simp only [crossEntropyGradient]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum, hdelta, sub_self, mul_zero]

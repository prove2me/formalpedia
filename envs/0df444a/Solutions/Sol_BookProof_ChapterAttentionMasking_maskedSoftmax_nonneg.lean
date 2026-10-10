-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.maskedSoftmax_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:06:21.8026+00:00
-- url     : https://prove2.me/submissions/99433b15-5c01-431b-ac43-6470b176f9ef

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.maskedSoftmax_nonneg
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_eq_zero_of_not_mem
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_pos_of_mem
open BookProof.ChapterAttentionMasking



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (j : Fin m) :
    0 ≤ maskedSoftmax beta s S j := by

  by_cases hj : j ∈ S
  · exact le_of_lt (maskedSoftmax_pos_of_mem beta s hj)
  · rw [maskedSoftmax_eq_zero_of_not_mem beta s hj]

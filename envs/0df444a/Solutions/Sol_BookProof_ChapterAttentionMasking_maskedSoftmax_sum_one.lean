-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:06:34.567614+00:00
-- url     : https://prove2.me/submissions/f86ac660-9d49-4eeb-9bcf-6fd71e5e5753
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.maskedSoftmax_sum_one
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedDenom_pos
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_of_mem
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_eq_zero_of_not_mem
open BookProof.ChapterAttentionMasking



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) : ∑ j, maskedSoftmax beta s S j = 1 := by

  have hne := ne_of_gt (maskedDenom_pos beta s hS)
  rw [← Finset.sum_subset (Finset.subset_univ S)
    (fun x _ hx => maskedSoftmax_eq_zero_of_not_mem beta s hx)]
  rw [Finset.sum_congr rfl fun j hj => maskedSoftmax_of_mem beta s hj, ← Finset.sum_div,
    div_self hne]

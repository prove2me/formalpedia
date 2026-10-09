-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.maskedSoftmax_restrict
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:06:38.121744+00:00
-- url     : https://prove2.me/submissions/cad37c4b-a287-4273-bb18-2b435483a7bc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.maskedSoftmax_restrict
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedDenom_pos
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_of_mem
open BookProof.ChapterAttentionMasking



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)}
    (hTS : T ⊆ S) {j : Fin m} (hj : j ∈ T) :
    maskedSoftmax beta s T j
      = maskedSoftmax beta s S j / ∑ l ∈ T, maskedSoftmax beta s S l := by

  have hS : (0 : ℝ) < ∑ l ∈ S, Real.exp (beta * s l) := maskedDenom_pos beta s ⟨j, hTS hj⟩
  have hT : (0 : ℝ) < ∑ l ∈ T, Real.exp (beta * s l) := maskedDenom_pos beta s ⟨j, hj⟩
  have hsum : ∑ l ∈ T, maskedSoftmax beta s S l
      = (∑ l ∈ T, Real.exp (beta * s l)) / ∑ l ∈ S, Real.exp (beta * s l) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun l hl => maskedSoftmax_of_mem beta s (hTS hl)
  rw [hsum, maskedSoftmax_of_mem beta s (hTS hj), maskedSoftmax_of_mem beta s hj,
    div_div_div_cancel_right₀ (ne_of_gt hS)]

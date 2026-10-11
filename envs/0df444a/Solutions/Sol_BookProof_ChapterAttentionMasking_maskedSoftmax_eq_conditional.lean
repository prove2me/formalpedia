-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:10.50109+00:00
-- url     : https://prove2.me/submissions/b59b276b-1d27-4d48-a0a8-e3c22fb63f51

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.maskedSoftmax_eq_conditional
import Mathlib
import Definitions.Def_ChapterAttentionMasking
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedDenom_pos
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_of_mem
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_denom_pos
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionMasking



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    {j : Fin m} (hj : j ∈ S) :
    maskedSoftmax beta s S j = scoreSoftmax beta s j / ∑ l ∈ S, scoreSoftmax beta s l := by

  have hZ : (0 : ℝ) < ∑ l, Real.exp (beta * s l) := scoreSoftmax_denom_pos beta s j
  have hS : (0 : ℝ) < ∑ l ∈ S, Real.exp (beta * s l) := maskedDenom_pos beta s ⟨j, hj⟩
  have hsum : ∑ l ∈ S, scoreSoftmax beta s l
      = (∑ l ∈ S, Real.exp (beta * s l)) / ∑ l, Real.exp (beta * s l) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => rfl
  rw [maskedSoftmax_of_mem beta s hj, hsum, scoreSoftmax,
    div_div_div_cancel_right₀ (ne_of_gt hZ)]

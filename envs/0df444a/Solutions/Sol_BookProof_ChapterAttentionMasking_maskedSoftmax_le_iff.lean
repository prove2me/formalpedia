-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.maskedSoftmax_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:06:36.949496+00:00
-- url     : https://prove2.me/submissions/c238cf55-e904-4511-ba40-393cb58245b0

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.maskedSoftmax_le_iff
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
theorem solution {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ)
    {S : Finset (Fin m)} {i j : Fin m} (hi : i ∈ S) (hj : j ∈ S) :
    maskedSoftmax beta s S i ≤ maskedSoftmax beta s S j ↔ s i ≤ s j := by

  have hS : (0 : ℝ) < ∑ l ∈ S, Real.exp (beta * s l) := maskedDenom_pos beta s ⟨j, hj⟩
  rw [maskedSoftmax_of_mem beta s hi, maskedSoftmax_of_mem beta s hj,
    div_le_div_iff_of_pos_right hS, Real.exp_le_exp,
    mul_le_mul_iff_of_pos_left hbeta]

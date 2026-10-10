-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.maskedSoftmax_odds
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:06:35.633139+00:00
-- url     : https://prove2.me/submissions/b13ee017-983b-4ed7-acef-196b3089d08b

-- Generated from ChapterAttentionMasking.lean — solution of BookProof.ChapterAttentionMasking.maskedSoftmax_odds
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
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} {i j : Fin m}
    (hi : i ∈ S) (hj : j ∈ S) :
    maskedSoftmax beta s S j * scoreSoftmax beta s i
      = maskedSoftmax beta s S i * scoreSoftmax beta s j := by

  have hS : (0 : ℝ) < ∑ l ∈ S, Real.exp (beta * s l) := maskedDenom_pos beta s ⟨j, hj⟩
  rw [maskedSoftmax_of_mem beta s hj, maskedSoftmax_of_mem beta s hi, scoreSoftmax, scoreSoftmax]
  field_simp

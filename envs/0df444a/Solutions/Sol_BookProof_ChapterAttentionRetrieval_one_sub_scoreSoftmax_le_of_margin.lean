-- Prove2me | solution 1 for BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:46:29.004449+00:00
-- url     : https://prove2.me/submissions/e742ab16-5cab-49cf-b071-a829e9d7b4a7

-- Generated from ChapterAttentionRetrieval.lean — solution of BookProof.ChapterAttentionRetrieval.one_sub_scoreSoftmax_le_of_margin
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_card_erase_cast
import Theorems.Thm_BookProof_ChapterAttentionRetrieval_scoreSoftmax_le_exp_neg_margin
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionRetrieval



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {beta delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) :
    1 - scoreSoftmax beta s j ≤ ((m : ℝ) - 1) * Real.exp (-(beta * delta)) := by

  have hsum : ∑ l, scoreSoftmax beta s l = 1 := scoreSoftmax_sum_one beta s j
  have hsplit : ∑ l ∈ Finset.univ.erase j, scoreSoftmax beta s l
      = 1 - scoreSoftmax beta s j := by
    have := Finset.add_sum_erase Finset.univ (fun l => scoreSoftmax beta s l)
      (Finset.mem_univ j)
    rw [hsum] at this
    linarith
  have hterm : ∀ l ∈ Finset.univ.erase j,
      scoreSoftmax beta s l ≤ Real.exp (-(beta * delta)) := fun l hl =>
    scoreSoftmax_le_exp_neg_margin hb s (hmargin l (Finset.mem_erase.1 hl).1)
  have hbound := Finset.sum_le_card_nsmul (Finset.univ.erase j)
    (fun l => scoreSoftmax beta s l) (Real.exp (-(beta * delta))) hterm
  rw [nsmul_eq_mul, card_erase_cast j, hsplit] at hbound
  exact hbound

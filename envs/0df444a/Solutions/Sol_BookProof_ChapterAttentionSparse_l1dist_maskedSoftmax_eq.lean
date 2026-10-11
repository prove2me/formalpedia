-- Prove2me | solution 1 for BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:47:46.485993+00:00
-- url     : https://prove2.me/submissions/7d82cbdb-2b00-4c5a-8efa-a22b82051e63

-- Generated from ChapterAttentionSparse.lean — solution of BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterAttentionSparse_attendedMass_pos
import Theorems.Thm_BookProof_ChapterAttentionSparse_attendedMass_le_one
import Theorems.Thm_BookProof_ChapterAttentionSparse_one_sub_attendedMass_eq
import Theorems.Thm_BookProof_ChapterAttentionSparse_maskedSoftmax_sub_of_mem
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_eq_zero_of_not_mem
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Definitions.Def_ChapterAttentionMarkov
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) (i : Fin m) :
    l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s)
      = 2 * (1 - attendedMass beta s S) := by

  have hP : 0 < attendedMass beta s S := attendedMass_pos beta s hS
  have hP1 : attendedMass beta s S ≤ 1 := attendedMass_le_one beta s S i
  have hin : ∑ j ∈ S, |maskedSoftmax beta s S j - scoreSoftmax beta s j|
      = 1 - attendedMass beta s S := by
    have hterm : ∀ j ∈ S, |maskedSoftmax beta s S j - scoreSoftmax beta s j|
        = scoreSoftmax beta s j * (1 - attendedMass beta s S) / attendedMass beta s S := by
      intro j hj
      rw [maskedSoftmax_sub_of_mem beta s hj, abs_of_nonneg]
      exact div_nonneg (mul_nonneg (scoreSoftmax_nonneg beta s j) (by linarith)) hP.le
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Finset.sum_mul, ← attendedMass]
    field_simp
  have hout : ∑ j ∈ Sᶜ, |maskedSoftmax beta s S j - scoreSoftmax beta s j|
      = 1 - attendedMass beta s S := by
    have hterm : ∀ j ∈ Sᶜ, |maskedSoftmax beta s S j - scoreSoftmax beta s j|
        = scoreSoftmax beta s j := by
      intro j hj
      rw [maskedSoftmax_eq_zero_of_not_mem beta s (Finset.mem_compl.1 hj), zero_sub, abs_neg,
        abs_of_nonneg (scoreSoftmax_nonneg beta s j)]
    rw [Finset.sum_congr rfl hterm, ← one_sub_attendedMass_eq beta s S i]
  have hsplit := Finset.sum_add_sum_compl S
    (fun j => |maskedSoftmax beta s S j - scoreSoftmax beta s j|)
  rw [l1dist, ← hsplit, hin, hout]
  ring

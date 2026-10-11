-- Prove2me | solution 1 for BookProof.ChapterAttentionSparse.one_sub_attendedMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:47:45.416274+00:00
-- url     : https://prove2.me/submissions/4662e7a3-0e95-45b7-be40-bae1906bb1cf

-- Generated from ChapterAttentionSparse.lean — solution of BookProof.ChapterAttentionSparse.one_sub_attendedMass_eq
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (S : Finset (Fin m)) (i : Fin m) :
    1 - attendedMass beta s S = ∑ l ∈ Sᶜ, scoreSoftmax beta s l := by

  have h := Finset.sum_add_sum_compl S (fun l => scoreSoftmax beta s l)
  rw [scoreSoftmax_sum_one beta s i] at h
  rw [attendedMass]
  linarith

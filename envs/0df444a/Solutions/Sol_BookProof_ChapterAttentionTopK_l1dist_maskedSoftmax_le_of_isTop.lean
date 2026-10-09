-- Prove2me | solution 1 for BookProof.ChapterAttentionTopK.l1dist_maskedSoftmax_le_of_isTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:45:09.809481+00:00
-- url     : https://prove2.me/submissions/a83a9198-f341-4bf7-ae38-db562a715aeb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionTopK.lean — solution of BookProof.ChapterAttentionTopK.l1dist_maskedSoftmax_le_of_isTop
import Mathlib
import Definitions.Def_ChapterAttentionTopK
import Theorems.Thm_BookProof_ChapterAttentionTopK_attendedMass_le_of_isTop
import Theorems.Thm_BookProof_ChapterAttentionSparse_l1dist_maskedSoftmax_eq
import Definitions.Def_ChapterAttentionMarkov
import Definitions.Def_ChapterAttentionMasking
import Theorems.Thm_BookProof_ChapterAttentionSparse_l1dist_maskedSoftmax_eq
open BookProof.ChapterAttentionSparse
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionTopK



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)}
    (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.card) (hSne : S.Nonempty)
    (hTne : T.Nonempty) (i : Fin m) :
    l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s)
      ≤ l1dist (maskedSoftmax beta s T) (scoreSoftmax beta s) := by

  rw [l1dist_maskedSoftmax_eq beta s hSne i, l1dist_maskedSoftmax_eq beta s hTne i]
  have := attendedMass_le_of_isTop beta s hS hcard
  linarith

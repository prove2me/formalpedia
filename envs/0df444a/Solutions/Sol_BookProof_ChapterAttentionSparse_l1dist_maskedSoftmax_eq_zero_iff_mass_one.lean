-- Prove2me | solution 1 for BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq_zero_iff_mass_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:41:37.451624+00:00
-- url     : https://prove2.me/submissions/dc5bd3b7-87be-41aa-aa92-8118cabeb996
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionSparse.lean — solution of BookProof.ChapterAttentionSparse.l1dist_maskedSoftmax_eq_zero_iff_mass_one
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterAttentionSparse_l1dist_maskedSoftmax_eq
import Definitions.Def_ChapterAttentionMarkov
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionMarkov
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ)
    {S : Finset (Fin m)} (hS : S.Nonempty) (i : Fin m) :
    l1dist (maskedSoftmax beta s S) (scoreSoftmax beta s) = 0
      ↔ attendedMass beta s S = 1 := by

  rw [l1dist_maskedSoftmax_eq beta s hS i]
  constructor <;> intro h <;> linarith

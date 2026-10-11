-- Prove2me | solution 1 for BookProof.ChapterAttentionSparse.attendedMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:47:27.954432+00:00
-- url     : https://prove2.me/submissions/55a98cfb-8452-4bc3-863e-37c3e395c999

-- Generated from ChapterAttentionSparse.lean — solution of BookProof.ChapterAttentionSparse.attendedMass_pos
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) :
    0 < attendedMass beta s S := by

  obtain ⟨i, hi⟩ := hS
  exact Finset.sum_pos' (fun l _ => (scoreSoftmax_pos beta s l).le)
    ⟨i, hi, scoreSoftmax_pos beta s i⟩

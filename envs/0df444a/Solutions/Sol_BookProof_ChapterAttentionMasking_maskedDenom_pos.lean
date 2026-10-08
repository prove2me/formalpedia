-- Prove2me | solution 1 for BookProof.ChapterAttentionMasking.maskedDenom_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T22:29:38.588272+00:00
-- url     : https://prove2.me/submissions/31258c69-c1c4-42d5-9824-3e9554a20cc0

import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterAttentionMasking

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterAttentionMasking in open BookProof.ChapterAttentionMasking in open scoped BigOperators in open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder in
theorem solution {m : ℕ} (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)} (hS : S.Nonempty) :
    0 < ∑ l ∈ S, Real.exp (beta * s l) := by
  intros
  positivity

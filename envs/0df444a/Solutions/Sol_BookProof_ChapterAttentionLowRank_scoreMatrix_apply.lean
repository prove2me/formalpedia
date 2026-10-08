-- Prove2me | solution 1 for BookProof.ChapterAttentionLowRank.scoreMatrix_apply
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T21:02:50.454979+00:00
-- url     : https://prove2.me/submissions/9b769575-e06a-471c-9408-e8e63f29799f

import Mathlib
import Definitions.Def_ChapterAttentionLowRank

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterAttentionLowRank in open BookProof.ChapterAttentionLowRank in open scoped BigOperators in
theorem solution {m d : ℕ} (Q K : Fin m → Fin d → ℝ) (i j : Fin m) :
    scoreMatrix Q K i j = ∑ a, Q i a * K j a := by
  intros
  rfl

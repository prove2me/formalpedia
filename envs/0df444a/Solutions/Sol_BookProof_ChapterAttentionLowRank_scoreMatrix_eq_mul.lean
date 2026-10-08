-- Prove2me | solution 1 for BookProof.ChapterAttentionLowRank.scoreMatrix_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T22:52:56.821844+00:00
-- url     : https://prove2.me/submissions/6ec43c1e-9497-40cc-9700-be46e7f3324d

import Mathlib
import Definitions.Def_ChapterAttentionLowRank

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterAttentionLowRank in open BookProof.ChapterAttentionLowRank in open scoped BigOperators in
theorem solution {m d : ℕ} (Q K : Fin m → Fin d → ℝ) :
    scoreMatrix Q K = (Matrix.of Q) * (Matrix.of K).transpose := by
  intros
  rfl

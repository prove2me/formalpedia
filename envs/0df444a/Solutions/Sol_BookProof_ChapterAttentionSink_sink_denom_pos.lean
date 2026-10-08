-- Prove2me | solution 1 for BookProof.ChapterAttentionSink.sink_denom_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T23:34:05.83999+00:00
-- url     : https://prove2.me/submissions/8ff3dec1-9c1f-4ad8-a9a1-407458d585e5

import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionSink

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterAttentionSink in open BookProof.ChapterAttentionSink in open scoped BigOperators in open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness in
theorem solution {m : ℕ} (beta s0 : ℝ) (s : Fin m → ℝ) :
    0 < Real.exp (beta * s0) + ∑ l, Real.exp (beta * s l) := by
  intros
  positivity

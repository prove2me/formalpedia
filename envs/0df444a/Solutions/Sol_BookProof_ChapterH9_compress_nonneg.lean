-- Prove2me | solution 1 for BookProof.ChapterH9.compress_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:03:16.677542+00:00
-- url     : https://prove2.me/submissions/0af37755-97f6-4a59-b611-de28b29dec97

import Definitions.Def_ChapterH4

open BookProof.ChapterH4 ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hX : ∀ x : E, 0 ≤ (inner ℂ x (X x) : ℂ).re) (y : F) :
    0 ≤ (inner ℂ y (compress V X y) : ℂ).re := by
  simpa only [compress, comp_apply, adjoint_inner_right] using hX (V y)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution

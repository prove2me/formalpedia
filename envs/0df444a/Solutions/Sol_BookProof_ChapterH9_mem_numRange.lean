-- Prove2me | solution 1 for BookProof.ChapterH9.mem_numRange
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:59:26.742108+00:00
-- url     : https://prove2.me/submissions/921e0bda-8e6b-42c5-ad43-103523d7ee6d

import Mathlib
import Definitions.Def_ChapterH9

open BookProof.ChapterH9

theorem solution {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {X : E →L[ℂ] E} (x : E) (hx : ‖x‖ = 1) :
    (inner ℂ x (X x) : ℂ) ∈ numRange X :=
  ⟨x, hx, rfl⟩

-- Prove2me | solution 1 for BookProof.ChapterH9.mem_numRange_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:59:27.357555+00:00
-- url     : https://prove2.me/submissions/bb62e32a-c4d3-495e-b13a-851795569335

import Mathlib
import Definitions.Def_ChapterH9

open BookProof.ChapterH9

theorem solution {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {X : E →L[ℂ] E} {c : ℂ} :
    c ∈ numRange X ↔ ∃ x : E, ‖x‖ = 1 ∧ (inner ℂ x (X x) : ℂ) = c :=
  Iff.rfl

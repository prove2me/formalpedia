-- Prove2me | solution 1 for BookProof.Complexification.Cx.ofReal_fixed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:07.66127+00:00
-- url     : https://prove2.me/submissions/e18ecd8c-0cbb-41e8-a510-3780d3e0cdef

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.ofReal_fixed
import Mathlib
import Definitions.Def_Complexification
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution (w : W) : cxConj (ofReal w) = ofReal w := by
 ext <;> simp

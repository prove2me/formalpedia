-- Prove2me | solution 1 for BookProof.Complexification.Cx.cxConj_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:04.897634+00:00
-- url     : https://prove2.me/submissions/a4212df1-1dfb-4c0a-8a24-7c1c3d76a056

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.cxConj_involutive
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
theorem solution (x : Cx W) : cxConj (cxConj x) = x := by
 ext <;> simp

-- Prove2me | solution 1 for BookProof.Complexification.Cx.cxMap_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:09.465175+00:00
-- url     : https://prove2.me/submissions/6f91c29a-0745-4a97-b80e-eba08ce4fb80

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.cxMap_add
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
theorem solution (m n : W →L[ℝ] W) : cxMap (m + n) = cxMap m + cxMap n := by

  ext x <;> simp

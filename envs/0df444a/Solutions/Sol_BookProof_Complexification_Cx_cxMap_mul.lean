-- Prove2me | solution 1 for BookProof.Complexification.Cx.cxMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:08.602633+00:00
-- url     : https://prove2.me/submissions/e06d869e-d44a-44dd-a4b9-c1863c6c8598

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.cxMap_mul
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
theorem solution (m n : W →L[ℝ] W) : cxMap (m * n) = cxMap m * cxMap n := by

  ext x <;> simp [ContinuousLinearMap.mul_apply]

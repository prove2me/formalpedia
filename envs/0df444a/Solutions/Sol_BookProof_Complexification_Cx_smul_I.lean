-- Prove2me | solution 1 for BookProof.Complexification.Cx.smul_I
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:03.873184+00:00
-- url     : https://prove2.me/submissions/190b67e3-9f3a-468b-ae4f-67d3041d84dd

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.smul_I
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
theorem solution (x : Cx W) : (Complex.I : ℂ) • x = ⟨-x.im, x.re⟩ := by
 ext <;> simp

-- Prove2me | solution 1 for BookProof.Complexification.Cx.cxConj_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:05.828627+00:00
-- url     : https://prove2.me/submissions/f849aef5-afab-4dcb-84d2-8b6a2e4cf193

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.cxConj_inner
import Mathlib
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution (x y : Cx W) :
    inner ℂ (cxConj x) (cxConj y) = starRingEnd ℂ (inner ℂ x y) := by

  simp only [inner_def, cxConj_apply]
  apply Complex.ext
  · simp [cxInner, inner_neg_left, inner_neg_right]
  · simp only [cxInner, inner_neg_left, inner_neg_right, Complex.conj_im]; ring

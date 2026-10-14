-- Prove2me | solution 1 for BookProof.Complexification.Cx.inner_im
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:02.165835+00:00
-- url     : https://prove2.me/submissions/7b5cc391-36eb-42fc-aad2-eed94584b397

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.inner_im
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
    RCLike.im (inner ℂ x y) = inner ℝ x.re y.im - inner ℝ x.im y.re := rfl

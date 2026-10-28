-- Prove2me | solution 1 for AvramDividend.Classical.exp_weighted_scale_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:08:15.872674+00:00
-- url     : https://prove2.me/submissions/2afd82fa-aae2-4139-93aa-53e7e0fd9c6a

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Set

theorem solution
    (W : ℝ → ℝ) (θ x : ℝ) (hW : DifferentiableAt ℝ W x) :
    HasDerivAt (fun y : ℝ => Real.exp (-(θ * y)) * W y)
      (Real.exp (-(θ * x)) * (deriv W x - θ * W x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(θ * y))) (Real.exp (-(θ * x)) * (-(θ * 1))) x :=
    ((hasDerivAt_id x).const_mul θ).neg.exp
  exact (h1.mul hW.hasDerivAt).congr_deriv (by ring)

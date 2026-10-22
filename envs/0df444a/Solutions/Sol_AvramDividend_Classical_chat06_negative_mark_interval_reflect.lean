-- Prove2me | solution 1 for AvramDividend.Classical.chat06_negative_mark_interval_reflect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:19:47.247159+00:00
-- url     : https://prove2.me/submissions/84f59a94-c1f8-40c5-bed7-e9cacfae9410

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory

namespace AvramChat06

/-- Reflecting the negative-uniform mark interval (-2,-1)
into the positive interval (1,2) preserves the exponential
Laplace integral without any factor, since the Jacobian has
absolute value one. -/
theorem negative_mark_interval_reflect (θ : ℝ) :
    (∫ y in (-2 : ℝ)..(-1 : ℝ), Real.exp (θ * y)) =
      ∫ x in (1 : ℝ)..2, Real.exp (-(θ * x)) := by
  have h := intervalIntegral.integral_comp_neg
    (f := fun y : ℝ => Real.exp (θ * y))
    (a := (1 : ℝ)) (b := (2 : ℝ))
  convert h.symm using 1
  congr 1
  funext x
  congr 1
  ring

end AvramChat06

open AvramChat06

theorem solution (θ : ℝ) :
    (∫ y in (-2 : ℝ)..(-1 : ℝ), Real.exp (θ * y)) =
      ∫ x in (1 : ℝ)..2, Real.exp (-(θ * x)) := by
  exact negative_mark_interval_reflect θ

-- Prove2me | solution 2 for AvramDividend.Classical.chat04_positive_discount_exponential_halfline_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:47:15.482026+00:00
-- url     : https://prove2.me/submissions/eca55479-da2c-40e6-aa0a-43f58571f6eb

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The scalar Laplace kernel integrates to the reciprocal positive rate. -/
theorem solution (p : ℝ) (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t))) = 1 / p := by
  have hneg : -p < 0 := by linarith
  have h := integral_exp_mul_Ioi hneg (0 : ℝ)
  simpa [neg_mul] using h

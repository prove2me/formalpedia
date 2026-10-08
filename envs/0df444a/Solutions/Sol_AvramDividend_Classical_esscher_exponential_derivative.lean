-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exponential_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:03:48.10341+00:00
-- url     : https://prove2.me/submissions/5dfdd48b-63b5-4820-a304-3c7cfdb5e89e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Derivative of the Esscher exponential weight on the real line. -/
theorem solution (φ x : ℝ) :
    deriv (fun y : ℝ => Real.exp (-φ * y)) x =
      Real.exp (-φ * x) * (-φ) := by
  have hl : DifferentiableAt ℝ (fun y : ℝ => (-φ) * y) x := by
    fun_prop
  rw [deriv_exp hl, deriv_const_mul_id]

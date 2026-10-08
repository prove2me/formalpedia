-- Prove2me | solution 1 for AvramDividend.Classical.weightedLaplace_integral_shift_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:09:04.076008+00:00
-- url     : https://prove2.me/submissions/bdf42a6d-1ef1-40b6-aa29-32afbfa21073

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (f : ℝ → ℝ) (θ y : ℝ) :
    (∫ x : ℝ, Real.exp (-(θ * x)) * f (x + y)) =
      Real.exp (θ * y) *
        (∫ x : ℝ, Real.exp (-(θ * x)) * f x) := by
  let g : ℝ → ℝ := fun x => Real.exp (-(θ * x)) * f x
  have he (x : ℝ) :
      Real.exp (-(θ * x)) * f (x + y) =
        Real.exp (θ * y) * g (x + y) := by
    dsimp [g]
    have hexp :
        Real.exp (-(θ * x)) =
          Real.exp (θ * y) * Real.exp (-(θ * (x + y))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  calc
    (∫ x : ℝ, Real.exp (-(θ * x)) * f (x + y)) =
        ∫ x : ℝ, Real.exp (θ * y) * g (x + y) := by
          congr 1
          funext x
          exact he x
    _ = Real.exp (θ * y) * (∫ x : ℝ, g (x + y)) := by
          rw [integral_const_mul]
    _ = Real.exp (θ * y) * (∫ x : ℝ, g x) := by
          rw [integral_add_right_eq_self]
    _ = Real.exp (θ * y) *
          (∫ x : ℝ, Real.exp (-(θ * x)) * f x) := rfl

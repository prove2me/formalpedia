-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_test_eq_on_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:47:56.547339+00:00
-- url     : https://prove2.me/submissions/338a42ea-e19e-4f9f-a41b-c45d8116a3d5

import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
The bounded full-line Laplace test is exactly the ordinary Laplace
kernel on the nonnegative support of the ladder-resolvent measures.
-/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (s x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-(s * max x 0)) = Real.exp (-(s * x)) := by
  rw [max_eq_left hx]

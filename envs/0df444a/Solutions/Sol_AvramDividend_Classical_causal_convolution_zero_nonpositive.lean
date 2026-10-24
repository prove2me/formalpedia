-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:12:56.639815+00:00
-- url     : https://prove2.me/submissions/12b441d3-d14c-4ff6-a46c-7e7df99e87d2

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Convolution of positive-time kernels is zero at nonpositive time. -/
theorem solution
    (f g : ℝ → ℝ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0)
    (hgzero : ∀ x : ℝ, x ≤ 0 → g x = 0)
    (x : ℝ) (hx : x ≤ 0) :
    (∫ y : ℝ, f y * g (x - y) ∂volume) = 0 := by
  have hzero : (fun y : ℝ => f y * g (x - y)) = fun _ => 0 := by
    funext y
    by_cases hy : y ≤ 0
    · simp [hfzero y hy]
    · have hxy : x - y ≤ 0 := by linarith
      simp [hgzero (x - y) hxy]
  simp [hzero]

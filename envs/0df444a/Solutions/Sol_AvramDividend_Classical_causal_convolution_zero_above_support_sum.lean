-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_zero_above_support_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:21:02.010119+00:00
-- url     : https://prove2.me/submissions/6f096773-ee30-42a9-80ab-513c2c992443

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The upper support bounds of the two convolution factors add. -/
theorem solution
    (f g : ℝ → ℝ) (a b x : ℝ)
    (hf : ∀ y : ℝ, a < y → f y = 0)
    (hg : ∀ z : ℝ, b < z → g z = 0)
    (h : a + b < x) :
    (∫ y : ℝ, f y * g (x - y) ∂volume) = 0 := by
  have hzero : (fun y : ℝ => f y * g (x - y)) = fun _ => 0 := by
    funext y
    by_cases hy : a < y
    · simp [hf y hy]
    · have hz : b < x - y := by linarith
      simp [hg (x - y) hz]
  simp [hzero]

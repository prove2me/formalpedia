-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_powers_nonnegative_on_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:33:29.127994+00:00
-- url     : https://prove2.me/submissions/f6784b96-79d2-4556-8536-c805a12d1075

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Causal convolution recursion preserves nonnegativity on nonnegative time. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in (0 : ℝ)..x,
        κ s * F n (x - s))
    (hκ : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t) :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      rw [hzero]
      exact hκ x hx
  | succ n ih =>
      intro x hx
      rw [hsucc n]
      apply intervalIntegral.integral_nonneg hx
      intro s hs
      apply mul_nonneg (hκ s hs.1)
      exact ih (x - s) (by linarith [hs.2])

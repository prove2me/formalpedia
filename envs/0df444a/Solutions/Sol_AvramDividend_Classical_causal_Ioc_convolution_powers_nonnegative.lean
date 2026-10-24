-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_convolution_powers_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:52:56.800844+00:00
-- url     : https://prove2.me/submissions/2cb5cda0-372c-4606-8e57-aace7bf0c4ec

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Set-integral recursive causal convolution preserves positivity. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        κ s * F n (x - s) ∂volume)
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
      change 0 ≤ ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume
      rw [← intervalIntegral.integral_of_le hx]
      apply intervalIntegral.integral_nonneg hx
      intro s hs
      exact mul_nonneg (hκ s hs.1)
        (ih (x - s) (by linarith [hs.2]))

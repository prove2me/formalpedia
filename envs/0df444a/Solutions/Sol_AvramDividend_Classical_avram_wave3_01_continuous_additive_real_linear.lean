-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_continuous_additive_real_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:18:09.824421+00:00
-- url     : https://prove2.me/submissions/4a4347a8-2e8f-44a7-955f-91c6f056e61f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The continuous real additive Cauchy equation has only linear solutions.
This converts a logarithmic first-record semigroup into an exponent. -/
theorem solution
    (g : ℝ → ℝ)
    (hadd : ∀ x y : ℝ, g (x + y) = g x + g y)
    (hcont : Continuous g) :
    ∀ x : ℝ, g x = x * g 1 := by
  let φ : ℝ →+ ℝ := {
    toFun := g
    map_zero' := by
      have h0 := hadd 0 0
      simp only [zero_add] at h0
      linarith
    map_add' := hadd
  }
  have hφ : Continuous (φ : ℝ → ℝ) := hcont
  intro x
  have hx := map_real_smul φ hφ x (1 : ℝ)
  change g (x • (1 : ℝ)) = x • g 1 at hx
  simpa only [smul_eq_mul, mul_one] using hx

-- Prove2me | solution 1 for AvramDividend.Classical.positive_density_preserves_infinite_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:47:35.517907+00:00
-- url     : https://prove2.me/submissions/f552a935-3bc6-4771-af5a-c3d5d0355ae3

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A uniformly nonzero density cannot make an infinite nonnegative integral finite. -/
theorem solution
    (ν : Measure ℝ) (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (c : ℝ≥0∞) (hc : c ≠ 0)
    (hlower : ∀ᵐ y : ℝ ∂ν, c ≤ f y)
    (hinf : (∫⁻ y : ℝ, g y ∂ν) = ⊤) :
    (∫⁻ y : ℝ, g y ∂(ν.withDensity f)) = ⊤ := by
  rw [lintegral_withDensity_eq_lintegral_mul ν hf hg]
  change (∫⁻ y : ℝ, f y * g y ∂ν) = ⊤
  have hpoint : ∀ᵐ y : ℝ ∂ν, c * g y ≤ f y * g y := by
    filter_upwards [hlower] with y hy
    exact mul_le_mul_of_nonneg_right hy (zero_le : (0 : ℝ≥0∞) ≤ g y)
  have hbound :
      (∫⁻ y : ℝ, c * g y ∂ν) ≤
        (∫⁻ y : ℝ, f y * g y ∂ν) :=
    lintegral_mono_ae hpoint
  have htop : (∫⁻ y : ℝ, c * g y ∂ν) = ⊤ := by
    rw [lintegral_const_mul c hg, hinf]
    simp [hc]
  exact top_unique (by simpa only [htop] using hbound)

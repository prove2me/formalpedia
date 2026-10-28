-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:22:21.672547+00:00
-- url     : https://prove2.me/submissions/47995526-f27b-4a6b-9bab-2ae20e10febc

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Increasing a nonnegative discount increases the scale function at every
positive reserve when the Lévy process has unbounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x → W₁ x ≤ W₂ x := by
  have hres := unbounded_scale_resolvent_convolution
    X hnbv q₁ q₂ hq₁ hq₂ W₁ W₂ hW₁ hW₂
  intro x hx
  have hC : 0 ≤ ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s) := by
    rw [← intervalIntegral.integral_of_le hx.le]
    apply intervalIntegral.integral_nonneg hx.le
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hxs : 0 ≤ x - s := sub_nonneg.mpr hs.2
    exact mul_nonneg (hW₁.2.1 s hs0) (hW₂.2.1 (x - s) hxs)
  have hprod : 0 ≤ (q₂ - q₁) *
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) :=
    mul_nonneg (sub_nonneg.mpr hq) hC
  linarith [hres x hx]

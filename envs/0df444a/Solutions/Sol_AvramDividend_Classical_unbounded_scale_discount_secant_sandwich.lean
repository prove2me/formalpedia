-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_secant_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:08:21.998979+00:00
-- url     : https://prove2.me/submissions/505c4e5c-f355-46f1-80c1-1f9f39739eea

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Discount secants are sandwiched by endpoint self-convolutions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ < q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₁ (x - s)) ≤
        (W₂ x - W₁ x) / (q₂ - q₁) ∧
      (W₂ x - W₁ x) / (q₂ - q₁) ≤
        ∫ s in Ioc (0 : ℝ) x, W₂ s * W₂ (x - s) := by
  intro x hx
  have hlo := unbounded_scale_discount_convolution_order
    X hnbv q₁ q₁ q₂ hq₁ hq₁ hq₂ le_rfl (le_of_lt hq)
    W₁ W₁ W₂ hW₁ hW₁ hW₂ x hx
  have hhi := unbounded_scale_discount_convolution_order
    X hnbv q₁ q₂ q₂ hq₁ hq₂ hq₂ (le_of_lt hq) le_rfl
    W₁ W₂ W₂ hW₁ hW₂ hW₂ x hx
  have hs := unbounded_scale_discount_secant_convolution
    X hnbv q₁ q₂ hq₁ hq₂ hq W₁ W₂ hW₁ hW₂ x hx
  constructor
  · rw [hs]
    exact hlo
  · rw [hs]
    exact hhi

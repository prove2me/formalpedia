-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_convolution_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:34:05.241962+00:00
-- url     : https://prove2.me/submissions/a4cfac30-c0ce-4e6a-adba-bbac54f902c8

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A strictly positive increase in the discount produces a strictly
positive scale-function causal convolution on every positive interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ < q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      0 < ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s) := by
  intro x hx
  have hsec := unbounded_scale_discount_secant_convolution
    X hnbv q₁ q₂ hq₁ hq₂ hq W₁ W₂ hW₁ hW₂ x hx
  have hstrict := unbounded_scale_discount_strict_monotone
    X hnbv q₁ q₂ hq₁ hq₂ hq W₁ W₂ hW₁ hW₂ x hx
  rw [← hsec]
  exact div_pos (sub_pos.mpr hstrict) (sub_pos.mpr hq)

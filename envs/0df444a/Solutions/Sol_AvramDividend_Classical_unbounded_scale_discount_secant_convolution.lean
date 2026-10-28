-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_secant_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:22:46.956589+00:00
-- url     : https://prove2.me/submissions/46e87177-7b7b-4823-83fa-046dcbfd76de

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The finite difference quotient in discount is exactly the positive
causal convolution of the two corresponding q-scale functions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hq : q₁ < q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      (W₂ x - W₁ x) / (q₂ - q₁) =
        ∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s) := by
  intro x hx
  have hq0 : q₂ - q₁ ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hres := unbounded_scale_resolvent_convolution
    X hnbv q₁ q₂ hq₁ hq₂ W₁ W₂ hW₁ hW₂ x hx
  apply (div_eq_iff hq0).2
  nlinarith [hres]

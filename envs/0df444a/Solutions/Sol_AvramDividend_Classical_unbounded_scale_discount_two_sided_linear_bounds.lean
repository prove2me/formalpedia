-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_two_sided_linear_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:31:34.775993+00:00
-- url     : https://prove2.me/submissions/04674e54-1705-4a4d-9eb3-b7e5b187def3

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_sandwich
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_uniform_secant_bound
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Two-sided linear discount changes are bounded by fixed endpoint convolutions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ Q : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hQ : 0 ≤ Q) (hq12 : q₁ < q₂) (hq2Q : q₂ ≤ Q)
    (W₀ W₁ W₂ WQ : ℝ → ℝ)
    (hW₀ : IsScaleFunction X 0 W₀)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hWQ : IsScaleFunction X Q WQ) :
    ∀ x : ℝ, 0 < x →
      (q₂ - q₁) *
        (∫ s in Ioc (0 : ℝ) x, W₀ s * W₀ (x - s)) ≤
          W₂ x - W₁ x ∧
      W₂ x - W₁ x ≤ (q₂ - q₁) *
        ∫ s in Ioc (0 : ℝ) x, WQ s * WQ (x - s) := by
  intro x hx
  have hfirst := unbounded_scale_discount_convolution_order
    X hnbv 0 0 q₁ (le_refl (0 : ℝ)) (le_refl (0 : ℝ)) hq₁
    le_rfl hq₁ W₀ W₀ W₁ hW₀ hW₀ hW₁ x hx
  have hsecond := unbounded_scale_discount_convolution_order
    X hnbv 0 q₁ q₁ (le_refl (0 : ℝ)) hq₁ hq₁
    hq₁ le_rfl W₀ W₁ W₁ hW₀ hW₁ hW₁ x hx
  have hs := unbounded_scale_discount_secant_sandwich
    X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ x hx
  have hdiv : (∫ s in Ioc (0 : ℝ) x, W₀ s * W₀ (x - s)) ≤
      (W₂ x - W₁ x) / (q₂ - q₁) :=
    (hfirst.trans hsecond).trans hs.1
  have hgappos : 0 < q₂ - q₁ := sub_pos.mpr hq12
  have hmul := (le_div_iff₀ hgappos).mp hdiv
  have hupper := unbounded_scale_discount_uniform_secant_bound
    X hnbv q₁ q₂ Q hq₁ hq₂ hQ hq12 hq2Q
    W₁ W₂ WQ hW₁ hW₂ hWQ x hx
  exact ⟨by simpa only [mul_comm] using hmul, hupper.2⟩

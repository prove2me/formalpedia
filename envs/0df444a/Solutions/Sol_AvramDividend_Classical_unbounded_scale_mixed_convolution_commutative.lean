-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_mixed_convolution_commutative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:12:30.393513+00:00
-- url     : https://prove2.me/submissions/41a1a108-11e9-4a7a-a623-336158053ea4

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The resolvent identity forces mixed scale-function convolution symmetry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hqne : q₁ ≠ q₂) (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂) :
    ∀ x : ℝ, 0 < x →
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) =
        ∫ s in Ioc (0 : ℝ) x, W₂ s * W₁ (x - s) := by
  intro x hx
  have h12 := unbounded_scale_resolvent_convolution
    X hnbv q₁ q₂ hq₁ hq₂ W₁ W₂ hW₁ hW₂ x hx
  have h21 := unbounded_scale_resolvent_convolution
    X hnbv q₂ q₁ hq₂ hq₁ W₂ W₁ hW₂ hW₁ x hx
  have hgap : q₂ - q₁ ≠ 0 := sub_ne_zero.mpr hqne.symm
  have hmul : (q₂ - q₁) *
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) =
        (q₂ - q₁) *
      (∫ s in Ioc (0 : ℝ) x, W₂ s * W₁ (x - s)) := by
    nlinarith [h12, h21]
  exact mul_left_cancel₀ hgap hmul

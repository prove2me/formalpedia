-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_strict_chord
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:07:46.672257+00:00
-- url     : https://prove2.me/submissions/be1502fa-4afe-45bf-8892-8b0f24a3d6d2

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_convex_secants
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Strict discount convexity in its weighted-chord formulation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ q₃ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq₃ : 0 ≤ q₃) (hq12 : q₁ < q₂) (hq23 : q₂ < q₃)
    (W₁ W₂ W₃ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hW₃ : IsScaleFunction X q₃ W₃) :
    ∀ x : ℝ, 0 < x →
      (q₃ - q₁) * W₂ x <
        (q₃ - q₂) * W₁ x + (q₂ - q₁) * W₃ x := by
  intro x hx
  have hslope := unbounded_scale_discount_strict_convex_secants
    X hnbv q₁ q₂ q₃ hq₁ hq₂ hq₃ hq12 hq23
    W₁ W₂ W₃ hW₁ hW₂ hW₃ x hx
  have hcross : (W₂ x - W₁ x) * (q₃ - q₂) <
      (W₃ x - W₂ x) * (q₂ - q₁) :=
    (div_lt_div_iff₀ (sub_pos.mpr hq12) (sub_pos.mpr hq23)).mp hslope
  nlinarith [hcross]

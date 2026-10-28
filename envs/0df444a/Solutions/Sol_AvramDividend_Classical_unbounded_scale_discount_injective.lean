-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:39:40.894306+00:00
-- url     : https://prove2.me/submissions/b88cbcfd-63ab-4f20-bdaf-7f4586e71938

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_strict_monotone
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For unbounded-variation paths, any single strictly positive reserve
identifies the nonnegative discount from the corresponding scale value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁) (hW₂ : IsScaleFunction X q₂ W₂)
    (x : ℝ) (hx : 0 < x) (heqW : W₁ x = W₂ x) :
    q₁ = q₂ := by
  by_cases hlt : q₁ < q₂
  · have hw := unbounded_scale_discount_strict_monotone
      X hnbv q₁ q₂ hq₁ hq₂ hlt W₁ W₂ hW₁ hW₂ x hx
    exact False.elim ((ne_of_lt hw) heqW)
  by_cases hgt : q₂ < q₁
  · have hw := unbounded_scale_discount_strict_monotone
      X hnbv q₂ q₁ hq₂ hq₁ hgt W₂ W₁ hW₂ hW₁ x hx
    exact False.elim ((ne_of_gt hw) heqW)
  exact le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)

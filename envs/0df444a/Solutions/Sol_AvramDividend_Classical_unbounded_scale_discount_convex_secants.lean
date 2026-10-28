-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_discount_convex_secants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:53:04.301196+00:00
-- url     : https://prove2.me/submissions/8eb98531-164d-4587-9769-cbe0f1c4afb8

import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_secant_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_discount_convolution_order
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The q-scale function is discretely convex in nonnegative discount:
its consecutive secant slopes are ordered. -/
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
      (W₂ x - W₁ x) / (q₂ - q₁) ≤
        (W₃ x - W₂ x) / (q₃ - q₂) := by
  intro x hx
  have hconv := unbounded_scale_discount_convolution_order
    X hnbv q₁ q₂ q₃ hq₁ hq₂ hq₃ hq12.le hq23.le
    W₁ W₂ W₃ hW₁ hW₂ hW₃ x hx
  have hsec12 := unbounded_scale_discount_secant_convolution
    X hnbv q₁ q₂ hq₁ hq₂ hq12 W₁ W₂ hW₁ hW₂ x hx
  have hsec23 := unbounded_scale_discount_secant_convolution
    X hnbv q₂ q₃ hq₂ hq₃ hq23 W₂ W₃ hW₂ hW₃ x hx
  calc
    (W₂ x - W₁ x) / (q₂ - q₁) =
      (∫ s in Ioc (0 : ℝ) x, W₁ s * W₂ (x - s)) := hsec12
    _ ≤ (∫ s in Ioc (0 : ℝ) x, W₂ s * W₃ (x - s)) := hconv
    _ = (W₃ x - W₂ x) / (q₃ - q₂) := hsec23.symm

-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_unique_function_nonnegative_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:22:56.37896+00:00
-- url     : https://prove2.me/submissions/a97e5642-339e-49a7-be7a-1b5cc4e730c8

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_unique_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The entire q-scale function is uniquely determined for nonnegative q. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q W₁)
    (hW₂ : IsScaleFunction X q W₂) :
    W₁ = W₂ := by
  funext x
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact (hW₁.1 x hneg).trans (hW₂.1 x hneg).symm
  · subst x
    have h01 := unbounded_scale_zero_origin_nonnegative_discount
      X hnbv q hq W₁ hW₁
    have h02 := unbounded_scale_zero_origin_nonnegative_discount
      X hnbv q hq W₂ hW₂
    exact h01.trans h02.symm
  · exact unbounded_scale_unique_nonnegative_discount
      X hnbv q hq W₁ W₂ hW₁ hW₂ x hpos

-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_zero_discount_C1_gaussian_constructed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:49:35.488338+00:00
-- url     : https://prove2.me/submissions/847e508a-f47d-4c02-b7e6-0e03030eb3a3

import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Gaussian unbounded-variation zero scale is C1 by constructed positive-scale existence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hσ : 0 < X.σ) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) := by
  apply unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
    X hnbv W₀ hW₀ hσ
  exact ⟨1, zero_lt_one,
    unbounded_positive_discount_scale_exists_from_zero
      X hnbv W₀ hW₀ 1 zero_lt_one⟩

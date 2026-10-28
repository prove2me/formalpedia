-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_finite_truncated_negative_tails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:22:55.691998+00:00
-- url     : https://prove2.me/submissions/c4026da6-4fc6-4f2e-b538-0d4e0e218fad

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_finite_of_unweighted
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ x : ℝ) (hφ : 0 ≤ φ) (hx : 0 < x) :
    (X.ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
      (Iio (-x)) < ⊤ := by
  have hfinite : X.ν (Iio (-x)) < ⊤ := by
    exact lt_of_le_of_lt
      (measure_mono (Set.Iio_subset_Iic_self))
      (negative_jump_truncation_measure_finite X.ν X.ν_integrable x hx)
  exact esscher_weighted_negative_tail_finite_of_unweighted
    X.ν φ x hφ hx hfinite

-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_running_infimum_law_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:42:07.300901+00:00
-- url     : https://prove2.me/submissions/28056e8e-0d17-4b9d-a310-0f96e3f1af96

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    IsProbabilityMeasure
      ((P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))).map
        (fun ω : Ω =>
          -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) := by
  letI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X t θ hθ
  exact Measure.isProbabilityMeasure_map
    (levy_running_infimum_measurable X t).aemeasurable

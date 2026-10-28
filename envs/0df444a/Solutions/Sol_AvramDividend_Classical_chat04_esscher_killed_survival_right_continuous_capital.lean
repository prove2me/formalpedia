-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_killed_survival_right_continuous_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:53:13.423972+00:00
-- url     : https://prove2.me/submissions/0de9136e-795b-4fb8-9009-22629c53f5ba

import Mathlib.Probability.CDF
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_running_infimum_law_probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_CDF_real_eq_survival_expectation
import Theorems.Thm_AvramDividend_Classical_probability_measure_real_Iic_right_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) (Ici x) x := by
  let μ : Measure ℝ := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))).map (fun ω : Ω => -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})
  letI : IsProbabilityMeasure μ :=
    chat04_esscher_running_infimum_law_probability X t θ hθ
  have heq :
      (fun y : ℝ => (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ y + X.X s ω}).indicator (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) =
      (fun y : ℝ => μ.real (Iic y)) := by
    funext y
    exact (chat04_esscher_reflected_CDF_real_eq_survival_expectation
      X t θ y hθ).symm
  rw [heq]
  exact probability_measure_real_Iic_right_continuous μ x

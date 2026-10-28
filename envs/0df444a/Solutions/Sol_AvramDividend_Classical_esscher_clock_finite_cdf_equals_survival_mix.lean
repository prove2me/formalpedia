-- Prove2me | solution 1 for AvramDividend.Classical.esscher_clock_finite_cdf_equals_survival_mix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:27:08.438772+00:00
-- url     : https://prove2.me/submissions/f62fe71b-b66d-4b7c-97ab-71046a16fda4

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_law_Iic_eq_killed_lintegral
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_real_to_lintegral
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The exact finite-rate reflected-infimum CDF mixture is the clock
    average of genuine weighted no-ruin survival probabilities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p x : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (∫⁻ t : ℝ,
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ θ))))
        {ω : Ω | -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal t ∧ y = X.X s ω} ≤ x}
      ∂expMeasure p) =
    (∫⁻ t : ℝ, ENNReal.ofReal
      (∫ ω, ({ω | ∀ s : ℝ≥0,
        s ≤ Real.toNNReal t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X (Real.toNNReal t) ω -
            (Real.toNNReal t : ℝ) * X.ψ θ)) ω ∂P)
      ∂expMeasure p) := by
  congr 1
  funext t
  have h := (chat04_esscher_reflected_law_Iic_eq_killed_lintegral
    X (Real.toNNReal t) θ x).trans
    (chat04_esscher_killed_survival_real_to_lintegral
      X x (Real.toNNReal t) θ hθ)
  rw [Measure.map_apply
    (levy_running_infimum_measurable X (Real.toNNReal t))
      measurableSet_Iic] at h
  exact h

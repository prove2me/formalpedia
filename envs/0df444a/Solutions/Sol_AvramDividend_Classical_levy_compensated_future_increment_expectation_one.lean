-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_future_increment_expectation_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:28:47.160977+00:00
-- url     : https://prove2.me/submissions/4c6e0dca-15cc-46e7-8865-00dd10c40ec2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp
      (θ * (X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.ψ θ) ∂P) = 1 := by
  let a : ℝ := ((t - s : ℝ≥0) : ℝ) * X.ψ θ
  have hm : Measurable (fun y : ℝ => Real.exp (θ * y - a)) := by
    fun_prop
  have hdist :=
    (X.stationaryIncrements s t hst).comp hm
  have heq :
      (∫ ω, Real.exp (θ * (X.X t ω - X.X s ω) - a) ∂P) =
        ∫ ω, Real.exp (θ * X.X (t - s) ω - a) ∂P := by
    simpa only [Function.comp_def] using hdist.integral_eq
  calc
    (∫ ω, Real.exp
      (θ * (X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.ψ θ) ∂P)
      = ∫ ω, Real.exp (θ * X.X (t - s) ω - a) ∂P := by
        simpa only [a] using heq
    _ = 1 := by
        simpa only [a] using
          (levy_compensated_exponential_expectation_one X (t - s) θ hθ)

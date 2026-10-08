-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_future_increment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:35:08.556137+00:00
-- url     : https://prove2.me/submissions/ade6c67a-1a9b-4a72-99cf-b0525a08203f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable

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
    Integrable (fun ω => Real.exp
      (θ * (X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.ψ θ)) P := by
  let a : ℝ := ((t - s : ℝ≥0) : ℝ) * X.ψ θ
  have hm : Measurable (fun y : ℝ => Real.exp (θ * y - a)) := by
    fun_prop
  have hdist :=
    (X.stationaryIncrements s t hst).comp hm
  have h0 : Integrable
      (fun ω => Real.exp (θ * X.X (t - s) ω - a)) P := by
    simpa only [a] using
      (levy_compensated_exponential_integrable X (t - s) θ hθ)
  have h1 : Integrable
      (fun ω => Real.exp (θ * (X.X t ω - X.X s ω) - a)) P := by
    simpa only [Function.comp_def] using (hdist.integrable_iff.mpr h0)
  simpa only [a] using h1

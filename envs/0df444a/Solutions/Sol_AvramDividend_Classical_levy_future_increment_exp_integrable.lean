-- Prove2me | solution 1 for AvramDividend.Classical.levy_future_increment_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:26:58.476406+00:00
-- url     : https://prove2.me/submissions/07c5cb3d-8ff7-4e64-821c-34464a80e85d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable
      (fun ω => Real.exp
        (θ * (X.X (s + h) ω - X.X s ω))) P := by
  have hs : s ≤ s + h :=
    le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ h by positivity)
  have hm : Measurable (fun y : ℝ => Real.exp (θ * y)) := by
    fun_prop
  have hdist := (X.stationaryIncrements s (s + h) hs).comp hm
  have hInt :
      Integrable
        (fun ω => Real.exp (θ * X.X ((s + h) - s) ω)) P :=
    (X.laplace ((s + h) - s) θ hθ).1
  simpa only [Function.comp_def] using (hdist.integrable_iff.mpr hInt)

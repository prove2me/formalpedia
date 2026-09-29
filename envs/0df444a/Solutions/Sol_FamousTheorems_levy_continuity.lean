-- Prove2me | solution 1 for FamousTheorems.levy_continuity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:20:55.438803+00:00
-- url     : https://prove2.me/submissions/26e2fef6-15db-412f-a21e-7138b13e70a7

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ₀ : MeasureTheory.ProbabilityMeasure E} {μ : ℕ → MeasureTheory.ProbabilityMeasure E} :
    Filter.Tendsto μ Filter.atTop (nhds μ₀) ↔
      ∀ t : E, Filter.Tendsto (fun n => MeasureTheory.charFun (μ n : MeasureTheory.Measure E) t) Filter.atTop
        (nhds (MeasureTheory.charFun (μ₀ : MeasureTheory.Measure E) t)) :=
  MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun

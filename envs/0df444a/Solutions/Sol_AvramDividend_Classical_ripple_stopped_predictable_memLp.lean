-- Prove2me | solution 1 for AvramDividend.Classical.ripple_stopped_predictable_memLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:14:45.522223+00:00
-- url     : https://prove2.me/submissions/79e2dc02-03cd-437c-9328-79fd69083c87

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable
import Theorems.Thm_AvramDividend_Classical_ripple_predictable_le_ambient_product

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- Restricting a predictable square-integrable integrand to (0, τ] preserves L².
Ported from Ripple/Stochastic/StoppedPredictableIntegrand.lean,
commit e216e28ce3ffb43877e11f71be260e40a37a35df, Apache-2.0. -/
theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    {ν : Measure ℝ≥0} {μ : Measure Ω}
    {H : ℝ≥0 × Ω → ℝ}
    (hτ : IsStoppingTime F τ)
    (hH : MemLp H 2 ((ν.prod μ).trim (ripple_predictable_le_ambient_product F))) :
    MemLp
      ({z : ℝ≥0 × Ω | 0 < z.1 ∧ (z.1 : WithTop ℝ≥0) ≤ τ z.2}.indicator H)
      2 ((ν.prod μ).trim (ripple_predictable_le_ambient_product F)) := by
  exact hH.indicator (ripple_stopping_region_predictable F τ hτ)


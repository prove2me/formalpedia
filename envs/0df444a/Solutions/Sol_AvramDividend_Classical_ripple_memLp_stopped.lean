-- Prove2me | solution 1 for AvramDividend.Classical.ripple_memLp_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:08:36.381091+00:00
-- url     : https://prove2.me/submissions/8f36cc5d-e45b-4ed0-84c2-2430dc75500d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable

open MeasureTheory Set

/-- Stopping retains predictable L² membership on the exact trimmed measure.
Adapted from Ripple/Stochastic/StoppedPredictableIntegrand.lean, Apache-2.0,
commit e216e28ce3ffb43877e11f71be260e40a37a35df. -/
theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (F : Filtration NNReal mΩ) (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime F τ)
    (hprod : F.predictable ≤ (inferInstance : MeasurableSpace (NNReal × Ω)))
    {ν : Measure NNReal} {μ : Measure Ω}
    {H : NNReal × Ω → ℝ}
    (hH : MemLp H 2 ((ν.prod μ).trim hprod)) :
    MemLp
      ({z : NNReal × Ω | 0 < z.1 ∧ (z.1 : WithTop NNReal) ≤ τ z.2}.indicator H)
      2 ((ν.prod μ).trim hprod) := by
  exact hH.indicator
    (AvramDividend.Classical.ripple_stopping_region_predictable F τ hτ)

-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_drift_increment_ae_fixed_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:11:19.670832+00:00
-- url     : https://prove2.me/submissions/e299ad8c-e716-42d2-aa5c-4fa6bef679df

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.OuterMeasure.AE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

/-- Actual BV Levy increments are below the deterministic drift increment at fixed times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂P,
      X.X t ω - X.X s ω ≤ ((t - s : ℝ≥0) : ℝ) * X.drift := by
  have hbase : P {ω : Ω |
      ((t - s : ℝ≥0) : ℝ) * X.drift < X.X (t - s) ω} = 0 := by
    have h := ae_iff.mp
      (bv_actual_levy_drift_upper_ae_fixed_time X hBV (t - s))
    simpa only [not_le] using h
  have heq := (X.stationaryIncrements s t hst).measure_mem_eq
    (s := Ioi (((t - s : ℝ≥0) : ℝ) * X.drift)) measurableSet_Ioi
  have htarget : P {ω : Ω |
      ((t - s : ℝ≥0) : ℝ) * X.drift < X.X t ω - X.X s ω} = 0 := by
    have heq' : P {ω : Ω |
        ((t - s : ℝ≥0) : ℝ) * X.drift < X.X t ω - X.X s ω} =
      P {ω : Ω |
        ((t - s : ℝ≥0) : ℝ) * X.drift < X.X (t - s) ω} := by
      simpa only [Set.preimage, Set.mem_Ioi] using heq
    exact heq'.trans hbase
  apply ae_iff.mpr
  simpa only [not_le] using htarget

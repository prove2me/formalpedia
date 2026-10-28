-- Prove2me | solution 1 for AvramDividend.Classical.actual_deficit_increment_small_positive_probability_stationary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:40:06.188922+00:00
-- url     : https://prove2.me/submissions/22b16849-90db-4eaf-9554-b4da616ddd04

import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual drift-deficit increment lies in a small positive interval
    with exactly the probability of a one-time deficit of the same duration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (b : ℝ) :
    P.real {ω : Ω |
      0 < (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω) ∧
      (X.drift * (t : ℝ) - X.X t ω) -
        (X.drift * (s : ℝ) - X.X s ω) ≤ b} =
    P.real {ω : Ω |
      0 < X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t - s) ω ∧
      X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t - s) ω ≤ b} := by
  have hIdent :=
    actual_levy_drift_deficit_stationary_increment_law X s t hst
  have hSet : MeasurableSet {z : ℝ | 0 < z ∧ z ≤ b} := by
    exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_le measurable_id measurable_const)
  have hMass := hIdent.measure_mem_eq hSet
  exact congrArg ENNReal.toReal (by
    simpa only [Set.preimage, Set.mem_setOf_eq] using hMass)

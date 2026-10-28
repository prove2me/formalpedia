-- Prove2me | solution 1 for AvramDividend.Classical.chat04_countable_shifted_future_reserve_upper_survival_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:43:18.886274+00:00
-- url     : https://prove2.me/submissions/2e9f4743-e1bb-40b6-bea8-c3f4f736d747

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Upper-barrier survival on any countable future schedule is Borel. -/
theorem solution
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) (a : ℝ) :
    MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → z.1 + z.2 (τ j) ≤ a} := by
  have e : {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → z.1 + z.2 (τ j) ≤ a} =
      ⋂ j : ℕ, {z : ℝ × (ℝ≥0 → ℝ) |
        τ j ≤ T → z.1 + z.2 (τ j) ≤ a} := by
    ext z
    simp
  rw [e]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : τ j ≤ T
  · simp only [hj, true_implies]
    exact measurableSet_le
      (measurable_fst.add ((measurable_pi_apply (τ j)).comp measurable_snd))
      measurable_const
  · simp [hj]

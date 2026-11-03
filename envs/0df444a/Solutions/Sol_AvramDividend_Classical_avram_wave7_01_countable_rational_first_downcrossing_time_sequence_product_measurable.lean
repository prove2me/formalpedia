-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_countable_rational_first_downcrossing_time_sequence_product_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:47:14.048623+00:00
-- url     : https://prove2.me/submissions/85ac2568-43a5-420c-9c52-8e566366ab39

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Every coordinate of the countable rational first-hit candidate time sequence is product-measurable. -/
theorem solution
    (grid : ℕ → ℝ≥0) (pairs : ℕ → ℕ × ℚ) :
    Measurable (fun Y : ℝ≥0 → ℝ => fun k : ℕ =>
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ |
          grid (pairs k).1 < grid n ∧
          Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal) := by
  apply measurable_pi_lambda
  intro k
  have hBase : Measurable (fun Y : ℝ≥0 → ℝ =>
      ⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ |
          grid (pairs k).1 < grid n ∧
          Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y) := by
    apply Measurable.iInf
    intro n
    have hx : Measurable (fun Y : ℝ≥0 → ℝ => Y (grid n)) :=
      measurable_pi_apply (grid n)
    have hState : MeasurableSet
        {Y : ℝ≥0 → ℝ | Y (grid n) < ((pairs k).2 : ℝ)} := by
      simpa only [Set.preimage, Set.mem_Iio, Set.mem_setOf_eq] using
        (measurableSet_Iio.preimage hx :
          MeasurableSet ((fun Y : ℝ≥0 → ℝ => Y (grid n)) ⁻¹'
            Iio ((pairs k).2 : ℝ)))
    have hs : MeasurableSet
        {Y : ℝ≥0 → ℝ |
          grid (pairs k).1 < grid n ∧ Y (grid n) < ((pairs k).2 : ℝ)} := by
      by_cases h : grid (pairs k).1 < grid n
      · simpa [h] using hState
      · simp only [h, false_and, setOf_false, MeasurableSet.empty]
    exact measurable_const.piecewise hs measurable_const
  exact ENNReal.measurable_toNNReal.comp hBase

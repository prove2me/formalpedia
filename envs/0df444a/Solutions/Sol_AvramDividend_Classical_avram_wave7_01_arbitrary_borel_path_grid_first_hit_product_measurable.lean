-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_arbitrary_borel_path_grid_first_hit_product_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:42:50.993858+00:00
-- url     : https://prove2.me/submissions/962f6b20-d730-4360-ba7f-a6bf6bbbd650

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The first countable grid visit to any Borel state set is a measurable path-coordinate functional. -/
theorem solution
    (B : Set ℝ) (hB : MeasurableSet B)
    (grid : ℕ → ℝ≥0) (s : ℝ≥0) :
    Measurable (fun Y : ℝ≥0 → ℝ =>
      (⨅ n : ℕ,
        {Y : ℝ≥0 → ℝ | s < grid n ∧ Y (grid n) ∈ B}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal) := by
  have hBase : Measurable (fun Y : ℝ≥0 → ℝ =>
      ⨅ n : ℕ,
        {Y : ℝ≥0 → ℝ | s < grid n ∧ Y (grid n) ∈ B}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y) := by
    apply Measurable.iInf
    intro n
    have hx : Measurable (fun Y : ℝ≥0 → ℝ => Y (grid n)) :=
      measurable_pi_apply (grid n)
    have hs : MeasurableSet
        {Y : ℝ≥0 → ℝ | s < grid n ∧ Y (grid n) ∈ B} := by
      by_cases h : s < grid n
      · simpa [Set.preimage, h] using hB.preimage hx
      · simp only [h, false_and, setOf_false, MeasurableSet.empty]
    exact measurable_const.piecewise hs measurable_const
  exact ENNReal.measurable_toNNReal.comp hBase

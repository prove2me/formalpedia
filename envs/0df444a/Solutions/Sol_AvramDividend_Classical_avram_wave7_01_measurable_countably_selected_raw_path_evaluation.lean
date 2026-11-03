-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_measurable_countably_selected_raw_path_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:56:16.683819+00:00
-- url     : https://prove2.me/submissions/c5a72bf3-5087-46fb-aba3-3c81e4417ba3

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Evaluating a raw coordinate path at a measurable countably selected grid index stays measurable. -/
theorem solution
    (grid : ℕ → ℝ≥0)
    (index : (ℝ≥0 → ℝ) → ℕ) (hIndex : Measurable index) :
    Measurable (fun Y : ℝ≥0 → ℝ => Y (grid (index Y))) := by
  classical
  have hPiece (n : ℕ) :
      Measurable (fun Y : ℝ≥0 → ℝ =>
        if n = index Y then Y (grid n) else (0 : ℝ)) := by
    have hs : MeasurableSet {Y : ℝ≥0 → ℝ | n = index Y} := by
      simpa [Set.preimage, eq_comm] using
        ((measurableSet_singleton n).preimage hIndex)
    exact (measurable_pi_apply (grid n)).ite hs measurable_const
  have hSum : Measurable (fun Y : ℝ≥0 → ℝ =>
      ∑' n : ℕ, if n = index Y then Y (grid n) else (0 : ℝ)) :=
    Measurable.tsum hPiece
  convert hSum using 1
  funext Y
  exact (tsum_ite_eq (index Y) (fun n : ℕ => Y (grid n))).symm

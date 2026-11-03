-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_measurable_right_grid_selector_for_jump_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:42:25.056181+00:00
-- url     : https://prove2.me/submissions/4f933f90-4832-4b3e-a57f-8e5e6d9bb552

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- A least Borel grid witness selects a point to the right of a random time. -/
theorem solution
    (grid : ℕ → ℝ≥0)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℝ≥0)
    (hExist : ∀ Y : ℝ≥0 → ℝ,
      ∃ n : ℕ, t Y < grid n ∧ grid n < t Y + ε) :
    ∃ index : (ℝ≥0 → ℝ) → ℕ,
      Measurable index ∧
      ∀ Y : ℝ≥0 → ℝ,
        t Y < grid (index Y) ∧ grid (index Y) < t Y + ε := by
  classical
  let p : (ℝ≥0 → ℝ) → ℕ → Prop := fun Y n =>
    t Y < grid n ∧ grid n < t Y + ε
  have hp : ∀ Y : ℝ≥0 → ℝ, ∃ n : ℕ, p Y n := hExist
  have hpMeas (n : ℕ) : MeasurableSet {Y : ℝ≥0 → ℝ | p Y n} := by
    have hLo : MeasurableSet {Y : ℝ≥0 → ℝ | t Y < grid n} := by
      have hI : MeasurableSet (Iio (grid n) : Set ℝ≥0) := measurableSet_Iio
      simpa only [Set.preimage, Set.mem_Iio] using hI.preimage ht
    have hHi : MeasurableSet {Y : ℝ≥0 → ℝ | grid n < t Y + ε} := by
      have hAdd : Measurable (fun Y : ℝ≥0 → ℝ => t Y + ε) :=
        ht.add measurable_const
      have hI : MeasurableSet (Ioi (grid n) : Set ℝ≥0) := measurableSet_Ioi
      simpa only [Set.preimage, Set.mem_Ioi] using hI.preimage hAdd
    exact hLo.inter hHi
  have hIndex : Measurable (fun Y : ℝ≥0 → ℝ => Nat.find (hp Y)) :=
    measurable_find hp hpMeas
  exact ⟨fun Y => Nat.find (hp Y), hIndex,
    fun Y => Nat.find_spec (hp Y)⟩

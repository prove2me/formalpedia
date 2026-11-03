-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_measurable_left_grid_selector_for_jump_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:42:13.053445+00:00
-- url     : https://prove2.me/submissions/8697b1a0-e5fa-4a34-9ef9-c195e5bcef0f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Measurably select a countable grid point immediately left of a random time. -/
theorem solution
    (grid : ℕ → ℝ≥0)
    (t : (ℝ≥0 → ℝ) → ℝ≥0) (ht : Measurable t)
    (ε : ℝ≥0)
    (hExist : ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
      ∃ n : ℕ, grid n < t Y ∧ t Y < grid n + ε) :
    ∃ index : (ℝ≥0 → ℝ) → ℕ,
      Measurable index ∧
      ∀ Y : ℝ≥0 → ℝ, 0 < t Y →
        grid (index Y) < t Y ∧ t Y < grid (index Y) + ε := by
  classical
  let p : (ℝ≥0 → ℝ) → ℕ → Prop := fun Y n =>
    (t Y = 0 ∧ n = 0) ∨
      (grid n < t Y ∧ t Y < grid n + ε)
  have hp (Y : ℝ≥0 → ℝ) : ∃ n : ℕ, p Y n := by
    by_cases hZero : t Y = 0
    · exact ⟨0, Or.inl ⟨hZero, rfl⟩⟩
    · have hPos : 0 < t Y := pos_iff_ne_zero.mpr hZero
      obtain ⟨n, hn⟩ := hExist Y hPos
      exact ⟨n, Or.inr hn⟩
  have hpMeas (n : ℕ) : MeasurableSet {Y : ℝ≥0 → ℝ | p Y n} := by
    have hZero : MeasurableSet {Y : ℝ≥0 → ℝ | t Y = 0} :=
      (measurableSet_singleton (0 : ℝ≥0)).preimage ht
    have hLo : MeasurableSet {Y : ℝ≥0 → ℝ | grid n < t Y} := by
      have hI : MeasurableSet (Ioi (grid n) : Set ℝ≥0) := measurableSet_Ioi
      simpa only [Set.preimage, Set.mem_Ioi] using hI.preimage ht
    have hHi : MeasurableSet {Y : ℝ≥0 → ℝ | t Y < grid n + ε} := by
      have hI : MeasurableSet (Iio (grid n + ε) : Set ℝ≥0) := measurableSet_Iio
      simpa only [Set.preimage, Set.mem_Iio] using hI.preimage ht
    have hFirst : MeasurableSet {Y : ℝ≥0 → ℝ | t Y = 0 ∧ n = 0} := by
      by_cases hn : n = 0
      · simpa [hn] using hZero
      · simpa [hn] using
          (MeasurableSet.empty : MeasurableSet (∅ : Set (ℝ≥0 → ℝ)))
    have hSecond : MeasurableSet
        {Y : ℝ≥0 → ℝ | grid n < t Y ∧ t Y < grid n + ε} :=
      hLo.inter hHi
    simpa only [p, Set.setOf_or] using hFirst.union hSecond
  have hIndex : Measurable (fun Y : ℝ≥0 → ℝ => Nat.find (hp Y)) :=
    measurable_find hp hpMeas
  refine ⟨fun Y => Nat.find (hp Y), hIndex, ?_⟩
  intro Y hPos
  have hSpec : p Y (Nat.find (hp Y)) := Nat.find_spec (hp Y)
  rcases hSpec with hZero | hGood
  · exact False.elim ((ne_of_gt hPos) hZero.1)
  · exact hGood

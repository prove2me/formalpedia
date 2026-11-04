-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_all_grid_sizes_cover_forces_no_source_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:18:54.300286+00:00
-- url     : https://prove2.me/submissions/f422baad-cff2-41b1-bd37-51d7121b30ae

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- A claim of covering jump times by m cells for every m forces no source jumps. -/
theorem solution
    (S : Set ℝ≥0) (grid : ℕ → ℕ → ℝ≥0)
    (hCover : ∀ m : ℕ, ∀ u : ℝ≥0, u ∈ S →
      ∃ i : ℕ, i < m ∧ u ∈ Set.Ioc (grid m i) (grid m (i + 1))) :
    S = ∅ := by
  ext u
  constructor
  · intro hu
    obtain ⟨i, hi, _⟩ := hCover 0 u hu
    omega
  · simp

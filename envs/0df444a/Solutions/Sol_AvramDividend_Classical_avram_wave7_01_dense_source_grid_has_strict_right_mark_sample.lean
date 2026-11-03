-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_dense_source_grid_has_strict_right_mark_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:05:22.269908+00:00
-- url     : https://prove2.me/submissions/418ebd0c-f389-4da3-9d78-588fb6fa9436

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Each strictly positive right neighbourhood of a raw source jump-time
selector contains a member of the fixed countable dense clock. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (t ε : ℝ≥0) (hε : 0 < ε) :
    ∃ n : ℕ, t < grid n ∧ grid n < t + ε := by
  have hInterval : t < t + ε := lt_add_of_pos_right t hε
  obtain ⟨n, hn⟩ :=
    hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hInterval)
  exact ⟨n, hn.1, hn.2⟩

-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_dense_source_grid_has_strict_left_mark_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:10:31.77907+00:00
-- url     : https://prove2.me/submissions/0c7249f6-5a56-4b1e-a5db-038ccb743fd9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Positive random jump times have left dense-grid samples at every
positive window size; this remains true when the window crosses zero. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (t ε : ℝ≥0) (ht : 0 < t) (hε : 0 < ε) :
    ∃ n : ℕ, grid n < t ∧ t < grid n + ε := by
  by_cases hεt : ε ≤ t
  · have hWindow : t - ε < t := tsub_lt_self ht hε
    obtain ⟨n, hn⟩ :=
      hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hWindow)
    refine ⟨n, hn.2, ?_⟩
    have hSub : ((t - ε : ℝ≥0) : ℝ) = (t : ℝ) - (ε : ℝ) :=
      NNReal.coe_sub hεt
    have hReal : (t : ℝ) < (grid n : ℝ) + (ε : ℝ) := by
      have hLow : ((t - ε : ℝ≥0) : ℝ) < (grid n : ℝ) :=
        NNReal.coe_lt_coe.mpr hn.1
      rw [hSub] at hLow
      linarith
    exact NNReal.coe_lt_coe.mp (by simpa only [NNReal.coe_add] using hReal)
  · have htε : t < ε := lt_of_not_ge hεt
    obtain ⟨n, hn⟩ :=
      hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr ht)
    refine ⟨n, hn.2, ?_⟩
    have hGrid0 : (0 : ℝ≥0) ≤ grid n := zero_le
    exact lt_of_lt_of_le htε (le_add_of_nonneg_left hGrid0)

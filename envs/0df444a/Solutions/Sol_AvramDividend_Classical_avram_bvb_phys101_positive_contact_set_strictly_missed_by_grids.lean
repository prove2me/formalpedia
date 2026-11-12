-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys101_positive_contact_set_strictly_missed_by_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:46:56.943264+00:00
-- url     : https://prove2.me/submissions/35ec1987-49bd-4eab-b151-df6987612312

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys100_compact_positive_contact_avoids_all_uniform_grid_points

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A positive-volume compact contact set can have strictly positive
distance at every sample in a countable collection of physical grids. -/
theorem solution (u : ℕ → ℕ → ℝ) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Icc (0 : ℝ) 1 ∧
      0 < (volume : Measure ℝ) K ∧
      ∀ n i : ℕ, 0 < Metric.infDist (u n i) K := by
  obtain ⟨K, hcompact, hbound, hdisj, hpos⟩ :=
    AvramDividend.Classical.avram_bvb_phys100_compact_positive_contact_avoids_all_uniform_grid_points u
  have hne : K.Nonempty := nonempty_of_measure_ne_zero (ne_of_gt hpos)
  refine ⟨K, hcompact, hbound, hpos, ?_⟩
  intro n i
  have hnot : u n i ∉ K := by
    intro hm
    exact (disjoint_left.mp hdisj) hm (mem_range_self (n, i))
  exact (hcompact.isClosed.notMem_iff_infDist_pos hne).mp hnot

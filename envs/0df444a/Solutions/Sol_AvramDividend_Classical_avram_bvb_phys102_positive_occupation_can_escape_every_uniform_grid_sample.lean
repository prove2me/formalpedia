-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys102_positive_occupation_can_escape_every_uniform_grid_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:55:34.292026+00:00
-- url     : https://prove2.me/submissions/52740c88-7b22-450e-bb06-5cddb1978de3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys100_compact_positive_contact_avoids_all_uniform_grid_points

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Point sampling on arbitrary countably many grids can miss a
positive-volume time set completely. -/
theorem solution (u : ℕ → ℕ → ℝ) :
    ∃ f : ℝ → ℝ,
      (∀ n i : ℕ, f (u n i) = 0) ∧
      {t : ℝ | f t = 1} ⊆ Icc (0 : ℝ) 1 ∧
      0 < (volume : Measure ℝ) {t : ℝ | f t = 1} := by
  classical
  obtain ⟨K, _, hbound, hdisj, hpos⟩ :=
    AvramDividend.Classical.avram_bvb_phys100_compact_positive_contact_avoids_all_uniform_grid_points u
  have hset : {t : ℝ | (if t ∈ K then (1 : ℝ) else 0) = 1} = K := by
    ext t
    by_cases h : t ∈ K <;> simp [h]
  refine ⟨(fun t => if t ∈ K then 1 else 0), ?_, ?_, ?_⟩
  · intro n i
    have hn : u n i ∉ K := by
      intro hmem
      exact (disjoint_left.mp hdisj) hmem (mem_range_self (n, i))
    simp [hn]
  · simpa [hset] using hbound
  · simpa [hset] using hpos

-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_compact_negative_support_separation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:55:54.11278+00:00
-- url     : https://prove2.me/submissions/63c02878-1727-4fe5-b1f4-28e91773184f

import Mathlib.Topology.Order.Compact
import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology

/-! Compact negative test support stays uniformly away from zero. -/
theorem solution
    (s : Set ℝ) (hs : IsCompact s)
    (hneg : s ⊆ Set.Iio (0 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ s, y ≤ -ε := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨x, hx, hmax⟩ :=
      hs.exists_isMaxOn hne (f := fun z : ℝ => z)
        continuous_id.continuousOn
    have hxneg : x < 0 := hneg hx
    refine ⟨-x / 2, by linarith, ?_⟩
    intro y hy
    have hle : y ≤ x := hmax hy
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, hy⟩).elim

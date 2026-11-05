-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_compact_test_left_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:57:45.597929+00:00
-- url     : https://prove2.me/submissions/dca326a0-927b-4972-b63f-441c7c87bba4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology

/-- Every compactly supported real marked test vanishes below some real
left endpoint, giving the lower support cut for a finite step partition. -/
theorem solution (f : ℝ → ℝ) (hfcomp : HasCompactSupport f) :
    ∃ L : ℝ, ∀ z : ℝ, z < L → f z = 0 := by
  obtain ⟨L, hL⟩ := hfcomp.isCompact.bddBelow
  refine ⟨L, ?_⟩
  intro z hz
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_le_of_gt hz) (hL hmem)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_compact_test_uniform_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:03:53.997994+00:00
-- url     : https://prove2.me/submissions/c42f6fdc-fd99-4e50-b36f-3238c31a34d7

import Mathlib.Topology.ContinuousMap.CompactlySupported

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology

/-- Compactly supported negative-mark tests have a positive bound,
    suitable for dominating source-original grid test sums. -/
theorem solution
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    ∃ M : ℝ, 0 < M ∧
      ∀ x : {x : ℝ // x < 0}, |f x| ≤ M := by
  obtain ⟨C, hC⟩ :=
    (f.hasCompactSupport).exists_bound_of_continuous f.continuous
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro x
  calc
    |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ C := hC x
    _ ≤ max C 1 := le_max_left C 1

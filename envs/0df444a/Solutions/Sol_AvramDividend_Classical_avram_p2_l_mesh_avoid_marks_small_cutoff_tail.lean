-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_avoid_marks_small_cutoff_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:48:35.671453+00:00
-- url     : https://prove2.me/submissions/59e2381d-353d-403b-8504-32bf673bd584

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_test_small_left_cutoff_strip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology AvramDividend.Classical

/-- The final negative interval-step endpoint can avoid every selected
intrinsic jump mark, even when a jump lies exactly at the nominal cutoff. -/
theorem solution (S : Finset ℝ) (f : ℝ → ℝ) (ρ ε : ℝ)
    (hε : 0 < ε) (hfcont : ContinuousAt f (-ρ))
    (hfzero : f (-ρ) = 0) :
    ∃ c : ℝ, c < -ρ ∧ c ∉ S ∧
      ∀ z : ℝ, c ≤ z → z ≤ -ρ → |f z| < ε := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    avram_p2_l_mesh_continuous_test_small_left_cutoff_strip
      f ρ ε hε hfcont hfzero
  obtain ⟨c, hcL, hcR, hcS⟩ :=
    avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
      S (-ρ - δ) (-ρ) (by linarith)
  refine ⟨c, hcR, hcS, ?_⟩
  intro z hcz hz
  exact hsmall z (lt_of_lt_of_le hcL hcz) hz

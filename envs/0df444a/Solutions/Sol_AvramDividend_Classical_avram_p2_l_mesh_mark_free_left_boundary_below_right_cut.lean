-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_mark_free_left_boundary_below_right_cut
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:10:11.889788+00:00
-- url     : https://prove2.me/submissions/a805ae20-6209-4d7d-b128-433da851553e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_left_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A mark-free zero-test left cut can precede any real right boundary. -/
theorem solution (S : Finset ℝ) (f : ℝ → ℝ)
    (hfcomp : HasCompactSupport f) (B : ℝ) :
    ∃ A : ℝ, A < B ∧ A ∉ S ∧ ∀ z : ℝ, z ≤ A → f z = 0 := by
  obtain ⟨L, hL⟩ := avram_p2_l_mesh_compact_test_left_tail_zero f hfcomp
  let C : ℝ := min L B
  obtain ⟨A, hAlow, hAhigh, hAnot⟩ :=
    avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
      S (C - 2) (C - 1) (by linarith)
  refine ⟨A, ?_, hAnot, ?_⟩
  · have hCB : C ≤ B := min_le_right L B
    linarith
  · intro z hz
    apply hL
    have hCL : C ≤ L := min_le_left L B
    linarith

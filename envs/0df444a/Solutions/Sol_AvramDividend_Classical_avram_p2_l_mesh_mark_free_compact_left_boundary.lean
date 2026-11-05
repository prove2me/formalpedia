-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_mark_free_compact_left_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:02:45.578197+00:00
-- url     : https://prove2.me/submissions/257ab265-ddbc-4bd7-9837-b397a17d1f18

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_left_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A compact real test has a support-free, finite-mark-free left cut. -/
theorem solution (S : Finset ℝ) (f : ℝ → ℝ)
    (hfcomp : HasCompactSupport f) :
    ∃ A : ℝ, A ∉ S ∧ ∀ z : ℝ, z ≤ A → f z = 0 := by
  obtain ⟨L, hL⟩ := avram_p2_l_mesh_compact_test_left_tail_zero f hfcomp
  obtain ⟨A, hAleft, hAright, hAnot⟩ :=
    avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
      S (L - 2) (L - 1) (by linarith)
  refine ⟨A, hAnot, ?_⟩
  intro z hz
  apply hL
  linarith

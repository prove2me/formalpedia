-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_continuous_negative_test_global_right_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:07:26.241208+00:00
-- url     : https://prove2.me/submissions/9bbfdae7-19ae-4f80-8629-207aebcc0f1a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_test_small_left_cutoff_strip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- The cutoff continuity strip extends to a globally small right tail. -/
theorem solution (f : ℝ → ℝ) (ρ η : ℝ) (hη : 0 < η)
    (hfcont : ContinuousAt f (-ρ)) (hfzero : f (-ρ) = 0)
    (hf : ∀ z : ℝ, -ρ < z → f z = 0) :
    ∃ B : ℝ, B < -ρ ∧ ∀ z : ℝ, B < z → |f z| ≤ η := by
  obtain ⟨δ, hδ, hstrip⟩ :=
    avram_p2_l_mesh_continuous_test_small_left_cutoff_strip
      f ρ η hη hfcont hfzero
  refine ⟨-ρ - δ / 2, by linarith, ?_⟩
  intro z hz
  by_cases hzr : z ≤ -ρ
  · have hlt : -ρ - δ < z := by linarith
    exact le_of_lt (hstrip z hlt hzr)
  · have hright : -ρ < z := lt_of_not_ge hzr
    rw [hf z hright, abs_zero]
    exact le_of_lt hη

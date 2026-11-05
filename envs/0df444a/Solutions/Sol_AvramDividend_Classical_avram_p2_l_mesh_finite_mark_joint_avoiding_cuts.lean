-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_finite_mark_joint_avoiding_cuts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:05:46.07536+00:00
-- url     : https://prove2.me/submissions/8a824137-60ce-431d-a50a-3dba03c2c0a1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped BigOperators Classical

/-- Simultaneously choose finitely indexed partition cuts in prescribed
open intervals, none of them equal to an intrinsic jump mark. -/
theorem solution {ι : Type*} (S : Finset ℝ)
    (a b : ι → ℝ) (hab : ∀ i : ι, a i < b i) :
    ∃ c : ι → ℝ, ∀ i : ι,
      a i < c i ∧ c i < b i ∧ c i ∉ S := by
  classical
  have hEach (i : ι) : ∃ c : ℝ,
      a i < c ∧ c < b i ∧ c ∉ S :=
    avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
      S (a i) (b i) (hab i)
  choose c hc using hEach
  exact ⟨c, hc⟩

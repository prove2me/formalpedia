-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:59:09.693682+00:00
-- url     : https://prove2.me/submissions/dcdfe991-9e95-4930-9f82-7060b089f1c2

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology

/-- A finite set of real jump marks cannot block every point of an open
interval. This permits step-test partition cuts to avoid the actual marks. -/
theorem solution (S : Finset ℝ) :
    ∀ a b : ℝ, a < b →
      ∃ c : ℝ, a < c ∧ c < b ∧ c ∉ S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro a b hab
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    exact ⟨c, hac, hcb, by simp⟩
  | @insert x s hx ih =>
    intro a b hab
    by_cases hax : a < x
    · by_cases hxb : x < b
      · obtain ⟨c, hac, hcx, hnot⟩ := ih a x hax
        refine ⟨c, hac, lt_trans hcx hxb, ?_⟩
        intro hm
        rcases Finset.mem_insert.mp hm with heq | hs
        · subst c
          exact (lt_irrefl x) hcx
        · exact hnot hs
      · obtain ⟨c, hac, hcb, hnot⟩ := ih a b hab
        refine ⟨c, hac, hcb, ?_⟩
        intro hm
        rcases Finset.mem_insert.mp hm with heq | hs
        · subst c
          exact (not_lt_of_ge (le_of_not_gt hxb)) hcb
        · exact hnot hs
    · obtain ⟨c, hac, hcb, hnot⟩ := ih a b hab
      refine ⟨c, hac, hcb, ?_⟩
      intro hm
      rcases Finset.mem_insert.mp hm with heq | hs
      · subst c
        exact hax hac
      · exact hnot hs

-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_finite_drawdown_strict_event_iff_reversed_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:15:30.517485+00:00
-- url     : https://prove2.me/submissions/39ee6b1b-3f0f-4fe7-b1cf-193652f08a1d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Finset Set
open scoped BigOperators

theorem solution (v : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    (∃ k : Fin n.succ,
      (∑ j ∈ Finset.range n, v j) -
        (∑ j ∈ Finset.range k.val, v j) < a) ↔
    (∃ k : Fin n.succ,
      (∑ j ∈ Finset.range k.val, v (n - 1 - j)) < a) := by
  have h := finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b v n
  constructor
  · rintro ⟨k, hk⟩
    have hm : ((∑ j ∈ Finset.range n, v j) -
        (∑ j ∈ Finset.range k.val, v j)) ∈
      Set.range (fun j : Fin n.succ =>
        ∑ x ∈ Finset.range j.val, v (n - 1 - x)) := by
      rw [← h]
      exact ⟨k, rfl⟩
    rcases hm with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simpa only [hj] using hk
  · rintro ⟨k, hk⟩
    have hm : (∑ j ∈ Finset.range k.val, v (n - 1 - j)) ∈
      Set.range (fun j : Fin n.succ =>
        (∑ x ∈ Finset.range n, v x) -
          (∑ x ∈ Finset.range j.val, v x)) := by
      rw [h]
      exact ⟨k, rfl⟩
    rcases hm with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simpa only [hj] using hk

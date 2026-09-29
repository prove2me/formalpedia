-- Prove2me | solution 1 for FamousTheorems.cauchy_cycle_type_count_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:46:50.031203+00:00
-- url     : https://prove2.me/submissions/05236939-24e1-4b73-89cb-ed6ae3133c92

import Mathlib

theorem solution (α : Type*) [DecidableEq α] [Fintype α] (m : Multiset ℕ) :
    ({g : Equiv.Perm α | g.cycleType = m} : Finset (Equiv.Perm α)).card =
      if m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α).factorial /
          ((Fintype.card α - m.sum).factorial * m.prod * ∏ n ∈ m.toFinset, (Multiset.count n m).factorial)
      else 0 :=
  Equiv.Perm.card_of_cycleType α m

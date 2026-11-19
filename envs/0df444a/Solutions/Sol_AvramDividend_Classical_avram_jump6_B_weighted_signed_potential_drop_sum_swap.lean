-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_weighted_signed_potential_drop_sum_swap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:09:28.849206+00:00
-- url     : https://prove2.me/submissions/48788bd0-b6e5-4b31-9253-c18b54b5ae22

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

theorem solution
    {ι : Type*} (s : Finset ι) (E A B : ι → ℝ) :
    (∑ i ∈ s, E i * (A i - B i)) =
      -(∑ i ∈ s, E i * (B i - A i)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end

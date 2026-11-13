-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_last_mesh_cell_positive_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:42:21.129302+00:00
-- url     : https://prove2.me/submissions/b76ddddd-03c8-4932-bbb9-4e5c8e826ffa

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- Split the extra terminal clipped cell from the paired spatial mesh sums. -/
theorem solution (m : ℕ) (a b c : ℕ → ℝ) :
    max ((∑ i ∈ Finset.range (m + 1), a i) -
      (∑ i ∈ Finset.range m, b i) -
      (∑ i ∈ Finset.range m, c i)) 0 ≤
    (∑ i ∈ Finset.range m, max (a i - b i - c i) 0) + max (a m) 0 := by
  have hid :
      (∑ i ∈ Finset.range (m + 1), a i) -
        (∑ i ∈ Finset.range m, b i) -
        (∑ i ∈ Finset.range m, c i) =
      (∑ i ∈ Finset.range m, (a i - b i - c i)) + a m := by
    simp only [Finset.sum_range_succ, Finset.sum_sub_distrib]
    ring
  rw [hid]
  apply max_le
  · exact add_le_add
      (Finset.sum_le_sum (fun i hi => le_max_left (a i - b i - c i) 0))
      (le_max_left (a m) 0)
  · exact add_nonneg
      (Finset.sum_nonneg (fun i hi => le_max_right (a i - b i - c i) 0))
      (le_max_right (a m) 0)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_strict_partition_cell_sum_eq_sample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:38:39.596718+00:00
-- url     : https://prove2.me/submissions/d8c414b9-1ec1-42aa-a954-0604cadaa3f8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped BigOperators

/-- An ordered half-open partition has one active test weight at each point. -/
theorem solution {n : ℕ} (a b c : Fin n → ℝ)
    (hordered : ∀ i j : Fin n, i < j → b i ≤ a j)
    (z : ℝ) (i : Fin n) (hi : z ∈ Ioc (a i) (b i)) :
    (∑ j : Fin n, if z ∈ Ioc (a j) (b j) then c j else 0) = c i := by
  classical
  have hother (j : Fin n) (hji : j ≠ i) : z ∉ Ioc (a j) (b j) := by
    intro hj
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hz : z ≤ a i := le_trans hj.2 (hordered j i hlt)
      exact (not_lt_of_ge hz) hi.1
    · have hz : z ≤ a j := le_trans hi.2 (hordered i j hgt)
      exact (not_lt_of_ge hz) hj.1
  calc
    (∑ j : Fin n, if z ∈ Ioc (a j) (b j) then c j else 0) =
        (if z ∈ Ioc (a i) (b i) then c i else 0) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact if_neg (hother j hji)
      · intro hiout
        exact False.elim (hiout (Finset.mem_univ i))
    _ = c i := if_pos hi

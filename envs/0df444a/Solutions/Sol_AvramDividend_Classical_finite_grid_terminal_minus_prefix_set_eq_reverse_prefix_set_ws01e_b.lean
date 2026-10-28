-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_terminal_minus_prefix_set_eq_reverse_prefix_set_ws01e_b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:39:10.682385+00:00
-- url     : https://prove2.me/submissions/0987258d-6925-421a-86bd-a4a48561d4dc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset

/-- Terminal-minus-prefix values of a finite walk are its reversed-prefix values. -/
theorem solution (v : ℕ → ℝ) (n : ℕ) :
    Set.range (fun k : Fin n.succ =>
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k.val) v) =
    Set.range (fun k : Fin n.succ =>
      Finset.sum (Finset.range k.val) (fun j => v (n - 1 - j))) := by
  have hs (k : ℕ) (hk : k ≤ n) :
      Finset.sum (Finset.range (n - k)) (fun j => v (n - 1 - j)) =
      Finset.sum (Finset.range n) v -
        Finset.sum (Finset.range k) v := by
    have hindex (j : ℕ) (hj : j ∈ Finset.range (n - k)) :
        n - 1 - j = k + (n - k - 1 - j) := by
      have hjlt : j < n - k := Finset.mem_range.mp hj
      omega
    calc
      _ = Finset.sum (Finset.range (n - k))
            (fun j => v (k + (n - k - 1 - j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hindex j hj]
      _ = Finset.sum (Finset.range (n - k)) (fun j => v (k + j)) :=
        Finset.sum_range_reflect (fun j => v (k + j)) (n - k)
      _ = _ := by
        have hsum := Finset.sum_range_add_sub_sum_range v k (n - k)
        rw [Nat.add_sub_of_le hk] at hsum
        exact hsum.symm
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨⟨n - k.val, by omega⟩, ?_⟩
    exact hs k.val (by omega)
  · rintro ⟨k, rfl⟩
    refine ⟨⟨n - k.val, by omega⟩, ?_⟩
    have h := hs (n - k.val) (Nat.sub_le n k.val)
    have hk : k.val ≤ n := by omega
    simpa only [Nat.sub_sub_self hk] using h.symm

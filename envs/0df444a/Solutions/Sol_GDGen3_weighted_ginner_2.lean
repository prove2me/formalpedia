-- Prove2me | solution 2 for GDGen3.weighted_ginner
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:29:18.380983+00:00
-- url     : https://prove2.me/submissions/e73fbb2a-a091-4f89-9cdc-a49dda186ada

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_sum_prefix_indicator

noncomputable section

open Finset

open GDGen3

theorem solution (h : ℝ) (N : ℕ) (L P : ℕ → ℕ → ℝ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), L i j * ginner h P i j) =
      h * ∑ j ∈ range (N + 1), ∑ k ∈ range (N + 1),
        ((if k < j then ∑ i ∈ range (N + 1), L i j else 0)
          - ∑ i ∈ range (N + 1), if k < i then L i j else 0) * P j k := by
  have hg : ∀ i ∈ range (N + 1), ∀ j ∈ range (N + 1),
      L i j * ginner h P i j = h * ∑ k ∈ range (N + 1),
        ((if k < j then L i j else 0) - (if k < i then L i j else 0)) * P j k := by
    intro i hi j hj
    unfold ginner
    rw [← sum_prefix_indicator (fun k => P j k) (N + 1) j (by exact le_of_lt (mem_range.mp hj)),
      ← sum_prefix_indicator (fun k => P j k) (N + 1) i (by exact le_of_lt (mem_range.mp hi))]
    rw [← mul_assoc]
    simp only [mul_sub, mul_sum, sum_sub_distrib, sub_mul]
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k hk
    split_ifs <;> ring
  rw [sum_congr rfl (fun i hi => sum_congr rfl (hg i hi))]
  simp only [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← sum_mul, sum_sub_distrib]
  congr 1
  by_cases hk : k < j <;> simp [hk]

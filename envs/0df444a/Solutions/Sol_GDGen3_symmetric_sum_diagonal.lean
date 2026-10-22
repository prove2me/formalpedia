-- Prove2me | solution 1 for GDGen3.symmetric_sum_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:59:31.735164+00:00
-- url     : https://prove2.me/submissions/85a86b24-107b-4835-990e-04960e1ccce5

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (B P : ℕ → ℕ → ℝ) (N : ℕ)
    (hP : ∀ i j, P i j = P j i)
    (hB : ∀ i j, i ≤ N → j ≤ N → i ≠ j → B i j + B j i = 0) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), B i j * P i j)
      = ∑ i ∈ range (N + 1), B i i * P i i := by
  let T := fun i j => if i = j then (0 : ℝ) else B i j * P i j
  have ht : ∀ i ∈ range (N + 1), ∀ j ∈ range (N + 1), T i j = -T j i := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j; simp [T]
    · simp only [T, if_neg hij, if_neg (Ne.symm hij)]
      rw [hP j i]
      have hb := hB i j (by simpa using hi) (by simpa using hj) hij
      linear_combination P i j * hb
  have hz : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) = 0 := by
    have he : (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) =
        -(∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) := by
      calc
        _ = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), -T j i := by
          apply sum_congr rfl; intro i hi
          apply sum_congr rfl; intro j hj
          exact ht i hi j hj
        _ = _ := by simp only [sum_neg_distrib]; rw [sum_comm]
    linarith
  have he : ∀ i ∈ range (N + 1), ∀ j ∈ range (N + 1),
      B i j * P i j = T i j + if i = j then B i i * P i i else 0 := by
    intro i hi j hj
    by_cases h : i = j <;> simp [T, h]
  rw [sum_congr rfl (fun i hi => sum_congr rfl (he i hi))]
  simp only [sum_add_distrib]
  rw [hz, zero_add]
  apply sum_congr rfl
  intro i hi
  simp [sum_ite_eq, hi]

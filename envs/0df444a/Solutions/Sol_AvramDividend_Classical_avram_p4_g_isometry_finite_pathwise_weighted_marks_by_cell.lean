-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_finite_pathwise_weighted_marks_by_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:56:25.284352+00:00
-- url     : https://prove2.me/submissions/b4712a39-d624-4af9-a3e4-47c1c49b4b59

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

/-- Exact finite pathwise weighted marked-jump count after disjoint cell assignment. -/
theorem solution
    {α : Type*} [DecidableEq α]
    (s : Finset α) (n : ℕ) (cell : α → Fin n) (w : Fin n → ℝ) :
    (∑ i : Fin n, w i * ((s.filter (fun a => cell a = i)).card : ℝ)) =
      ∑ a ∈ s, w (cell a) := by
  classical
  have hCard (i : Fin n) :
      ((s.filter (fun a => cell a = i)).card : ℝ) =
      ∑ a ∈ s, if cell a = i then (1 : ℝ) else 0 := by
    have hNat := Finset.card_filter (fun a => cell a = i) s
    exact_mod_cast hNat
  calc
    (∑ i : Fin n, w i * ((s.filter (fun a => cell a = i)).card : ℝ)) =
        ∑ i : Fin n, ∑ a ∈ s, if cell a = i then w i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hCard, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp
    _ = ∑ a ∈ s, ∑ i : Fin n, if cell a = i then w i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ s, w (cell a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp

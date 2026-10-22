-- Prove2me | solution 1 for FairRandomObject.Bads.step_2_theta_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:53:00.225865+00:00
-- url     : https://prove2.me/submissions/8ff0115f-fbe2-4e9c-995c-ba2eb859fe4a

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy

open FairRandomObject.Bads

theorem solution {n : ℕ} (hn : 2 ≤ n) (ϕ : Rule n) (hϕ : IsAPIRule ϕ)
    (h9 : Satisfies9 ϕ 0) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    ϕ x = equalSplit n x := by
  have hx0 : 0 ≤ x := fun i => (hx i).le
  have hle : ∀ i, ϕ x i ≤ 1 / n := by
    intro i
    have := h9 x hx0 i
    unfold bound9 at this
    rw [if_neg (hx i).ne', zero_div, zero_mul, add_zero] at this
    exact le_trans this (min_le_left _ _)
  have hsum : ∑ i, ϕ x i = 1 := (hϕ.2 x hx0).2
  funext i
  simp only [equalSplit]
  by_contra hne
  have hlt : ϕ x i < 1 / n := lt_of_le_of_ne (hle i) hne
  have : ∑ j, ϕ x j < ∑ _j : Fin n, (1 / (n:ℝ)) :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hlt⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum] at this
  have hn' : (n:ℝ) ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp at this
  linarith

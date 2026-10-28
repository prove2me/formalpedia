-- Prove2me | solution 1 for BudgetCournot.Equilibrium.H_least_feasible_B17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:14:32.193116+00:00
-- url     : https://prove2.me/submissions/ea17984d-aeec-4414-84d3-81674d45ffbe

import Mathlib
import Definitions.Def_BudgetCournot_Equilibrium_Model

open Finset

open BudgetCournot.Equilibrium in
theorem solution {M : ℕ} (R β : Fin M → ℝ) (hR : Monotone R)
    (hR0 : ∀ j, 0 ≤ R j) (hβ : ∀ j, 0 < β j) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ H R β x ∧ ∑ j, β j * max (R j - H R β x) 0 ≤ x ∧
      (∀ z : ℝ, 0 ≤ z → ∑ j, β j * max (R j - z) 0 ≤ x → H R β x ≤ z) ∧
      (H R β x = 0 ∨ ∑ j, β j * max (R j - H R β x) 0 = x) := by
  set F : ℝ → ℝ := fun z => ∑ j, β j * max (R j - z) 0 with hF
  set A : Set ℝ := {z : ℝ | 0 ≤ z ∧ ∑ j, β j * max (R j - z) 0 ≤ x} with hA
  have hH : H R β x = sInf A := rfl
  have Fc : Continuous F := by
    apply continuous_finset_sum
    intro j _
    exact continuous_const.mul ((continuous_const.sub continuous_id).max continuous_const)
  have Aclosed : IsClosed A :=
    (isClosed_le continuous_const continuous_id).inter (isClosed_le Fc continuous_const)
  have Ane : A.Nonempty := by
    refine ⟨∑ j, R j, sum_nonneg (fun j _ => hR0 j), ?_⟩
    have : ∑ j, β j * max (R j - ∑ k, R k) 0 = 0 := by
      apply sum_eq_zero
      intro j _
      have : R j ≤ ∑ k, R k := single_le_sum (fun k _ => hR0 k) (mem_univ j)
      rw [max_eq_right (by linarith)]
      ring
    rw [this]
    exact hx
  have Abdd : BddBelow A := ⟨0, fun z hz => hz.1⟩
  have hmem : sInf A ∈ A := Aclosed.csInf_mem Ane Abdd
  rw [hH]
  refine ⟨hmem.1, hmem.2, fun z hz hzx => csInf_le Abdd ⟨hz, hzx⟩, ?_⟩
  by_contra hc
  push_neg at hc
  obtain ⟨h0, hne⟩ := hc
  set Hs := sInf A with hHs
  have hpos : 0 < Hs := lt_of_le_of_ne hmem.1 (Ne.symm h0)
  have hlt : F Hs < x := lt_of_le_of_ne hmem.2 hne
  set B := ∑ j, β j with hB
  have hB0 : 0 ≤ B := sum_nonneg (fun j _ => (hβ j).le)
  set δ := min Hs ((x - F Hs) / (B + 1)) with hδ
  have hq : 0 < (x - F Hs) / (B + 1) := div_pos (by linarith) (by linarith)
  have hδpos : 0 < δ := lt_min hpos hq
  have hδ1 : δ ≤ Hs := min_le_left _ _
  have hδ2 : δ ≤ (x - F Hs) / (B + 1) := min_le_right _ _
  have hbound : F (Hs - δ) ≤ F Hs + δ * B := by
    simp only [hF, hB]
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro j _
    have : max (R j - (Hs - δ)) 0 ≤ max (R j - Hs) 0 + δ :=
      max_le (by linarith [le_max_left (R j - Hs) 0]) (by linarith [le_max_right (R j - Hs) 0])
    nlinarith [hβ j]
  have hδB : δ * B < x - F Hs := by
    have : δ * (B + 1) ≤ x - F Hs := by
      rw [le_div_iff₀ (by linarith)] at hδ2
      exact hδ2
    nlinarith
  have hmemz : Hs - δ ∈ A := ⟨by linarith, by
    show F (Hs - δ) ≤ x
    linarith⟩
  have := csInf_le Abdd hmemz
  linarith

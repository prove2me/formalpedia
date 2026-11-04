-- Prove2me | solution 1 for CoffmanMitrani.ineq_818_product
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T04:04:27.483209+00:00
-- url     : https://prove2.me/submissions/0d4ca41f-f3df-4b33-860c-e8de7c6d96bc

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_rho

set_option autoImplicit false

open Finset

theorem cm_fc6b9ade_aux {ι : Type} [DecidableEq ι] (r : ι → ℝ) (hpos : ∀ i, 0 < r i)
    (g₁ g₂ : Finset ι) (h₁ : (g₁ \ g₂).Nonempty) (h₂ : (g₂ \ g₁).Nonempty) :
    (1 - ∑ i ∈ g₁ ∪ g₂, r i) * (1 - ∑ i ∈ g₁ ∩ g₂, r i) <
      (1 - ∑ i ∈ g₁, r i) * (1 - ∑ i ∈ g₂, r i) := by
  have hA : 0 < ∑ i ∈ g₁ \ g₂, r i := Finset.sum_pos (fun i _ => hpos i) h₁
  have hB : 0 < ∑ i ∈ g₂ \ g₁, r i := Finset.sum_pos (fun i _ => hpos i) h₂
  have e1 := Finset.sum_inter_add_sum_sdiff g₁ g₂ r
  have e2 := Finset.sum_inter_add_sum_sdiff g₂ g₁ r
  have e3 := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := r)
  rw [Finset.inter_comm g₂ g₁] at e2
  generalize ∑ i ∈ g₁ ∪ g₂, r i = U at e3 ⊢
  generalize ∑ i ∈ g₁ ∩ g₂, r i = C at e1 e2 e3 ⊢
  generalize ∑ i ∈ g₁ \ g₂, r i = A at hA e1 ⊢
  generalize ∑ i ∈ g₂ \ g₁, r i = B at hB e2 ⊢
  generalize ∑ i ∈ g₁, r i = S₁ at e1 e3 ⊢
  generalize ∑ i ∈ g₂, r i = S₂ at e2 e3 ⊢
  have hU : U = C + A + B := by linarith
  subst hU e1 e2
  have key : (1 - (C + A)) * (1 - (C + B)) - (1 - (C + A + B)) * (1 - C) = A * B := by ring
  have hAB : 0 < A * B := mul_pos hA hB
  linarith

open CoffmanMitrani in
theorem solution (D : Data) (g1 g2 : Finset (Fin D.M))
    (h1 : (g1 \ g2).Nonempty) (h2 : (g2 \ g1).Nonempty) :
    (1 - ∑ i ∈ g1 ∪ g2, D.rho i) * (1 - ∑ i ∈ g1 ∩ g2, D.rho i) <
      (1 - ∑ i ∈ g1, D.rho i) * (1 - ∑ i ∈ g2, D.rho i) := by
  have hpos : ∀ i, 0 < D.rho i := by
    intro i
    unfold Data.rho
    exact div_pos (D.lam_pos i) (D.mu_pos i)
  exact cm_fc6b9ade_aux D.rho hpos g1 g2 h1 h2

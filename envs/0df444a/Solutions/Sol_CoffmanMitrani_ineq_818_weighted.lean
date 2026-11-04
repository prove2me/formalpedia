-- Prove2me | solution 1 for CoffmanMitrani.ineq_818_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T04:04:27.843917+00:00
-- url     : https://prove2.me/submissions/5e466d78-0539-4cd3-81a1-4d9bfd8bc863

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_rho

set_option autoImplicit false

open Finset

theorem cm_550ecf09_aux {ι : Type} [DecidableEq ι] (a r : ι → ℝ)
    (a_pos : ∀ i, 0 < a i) (rho_pos : ∀ i, 0 < r i)
    (g₁ g₂ : Finset ι) (h₁ : (g₁ \ g₂).Nonempty) (h₂ : (g₂ \ g₁).Nonempty) :
    (∑ i ∈ g₁, a i) * (1 - ∑ i ∈ g₂, r i) + (∑ i ∈ g₂, a i) * (1 - ∑ i ∈ g₁, r i)
        - (∑ i ∈ g₁ ∩ g₂, a i) * (1 - ∑ i ∈ g₁ ∪ g₂, r i) <
      (∑ i ∈ g₁ ∪ g₂, a i) * (1 - ∑ i ∈ g₁ ∩ g₂, r i) := by
  have hA1 : 0 < ∑ i ∈ g₁ \ g₂, a i := Finset.sum_pos (fun i _ => a_pos i) h₁
  have hA2 : 0 < ∑ i ∈ g₂ \ g₁, a i := Finset.sum_pos (fun i _ => a_pos i) h₂
  have hR1 : 0 < ∑ i ∈ g₁ \ g₂, r i := Finset.sum_pos (fun i _ => rho_pos i) h₁
  have hR2 : 0 < ∑ i ∈ g₂ \ g₁, r i := Finset.sum_pos (fun i _ => rho_pos i) h₂
  have e1a := Finset.sum_inter_add_sum_sdiff g₁ g₂ a
  have e2a := Finset.sum_inter_add_sum_sdiff g₂ g₁ a
  have e1r := Finset.sum_inter_add_sum_sdiff g₁ g₂ r
  have e2r := Finset.sum_inter_add_sum_sdiff g₂ g₁ r
  have eua := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := a)
  have eur := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := r)
  rw [Finset.inter_comm g₂ g₁] at e2a e2r
  generalize ∑ i ∈ g₁ ∪ g₂, a i = Ua at eua ⊢
  generalize ∑ i ∈ g₁ ∪ g₂, r i = Ur at eur ⊢
  generalize ∑ i ∈ g₁ ∩ g₂, a i = Ca at e1a e2a eua ⊢
  generalize ∑ i ∈ g₁ ∩ g₂, r i = Cr at e1r e2r eur ⊢
  generalize ∑ i ∈ g₁ \ g₂, a i = A1 at hA1 e1a ⊢
  generalize ∑ i ∈ g₂ \ g₁, a i = A2 at hA2 e2a ⊢
  generalize ∑ i ∈ g₁ \ g₂, r i = R1 at hR1 e1r ⊢
  generalize ∑ i ∈ g₂ \ g₁, r i = R2 at hR2 e2r ⊢
  generalize ∑ i ∈ g₁, a i = S1a at e1a eua ⊢
  generalize ∑ i ∈ g₂, a i = S2a at e2a eua ⊢
  generalize ∑ i ∈ g₁, r i = S1r at e1r eur ⊢
  generalize ∑ i ∈ g₂, r i = S2r at e2r eur ⊢
  have hUa : Ua = Ca + A1 + A2 := by linarith
  have hUr : Ur = Cr + R1 + R2 := by linarith
  subst hUa hUr e1a e2a e1r e2r
  have key : (Ca + A1 + A2) * (1 - Cr) -
      ((Ca + A1) * (1 - (Cr + R2)) + (Ca + A2) * (1 - (Cr + R1))
        - Ca * (1 - (Cr + R1 + R2))) = A1 * R2 + A2 * R1 := by ring
  have k1 := mul_pos hA1 hR2
  have k2 := mul_pos hA2 hR1
  linarith

open CoffmanMitrani in
theorem solution (D : Data) (g1 g2 : Finset (Fin D.M))
    (h1 : (g1 \ g2).Nonempty) (h2 : (g2 \ g1).Nonempty) :
    (∑ i ∈ g1, D.rho i / D.mu i) * (1 - ∑ i ∈ g2, D.rho i) +
        (∑ i ∈ g2, D.rho i / D.mu i) * (1 - ∑ i ∈ g1, D.rho i) -
        (∑ i ∈ g1 ∩ g2, D.rho i / D.mu i) * (1 - ∑ i ∈ g1 ∪ g2, D.rho i) <
      (∑ i ∈ g1 ∪ g2, D.rho i / D.mu i) * (1 - ∑ i ∈ g1 ∩ g2, D.rho i) := by
  have hpos : ∀ i, 0 < D.rho i := by
    intro i
    unfold Data.rho
    exact div_pos (D.lam_pos i) (D.mu_pos i)
  have hapos : ∀ i, 0 < D.rho i / D.mu i := fun i => div_pos (hpos i) (D.mu_pos i)
  exact cm_550ecf09_aux (fun i => D.rho i / D.mu i) D.rho hapos hpos g1 g2 h1 h2

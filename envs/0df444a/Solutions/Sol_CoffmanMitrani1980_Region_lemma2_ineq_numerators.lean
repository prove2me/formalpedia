-- Prove2me | solution 1 for CoffmanMitrani1980.Region.lemma2_ineq_numerators
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:52:16.723495+00:00
-- url     : https://prove2.me/submissions/678e3fa7-15af-4162-8b7e-77610c50e961

import Mathlib
import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

open CoffmanMitrani1980.Region in
theorem solution {M : ℕ} (p : Params M) (g₁ g₂ : Finset (Fin M))
    (h₁ : (g₁ \ g₂).Nonempty) (h₂ : (g₂ \ g₁).Nonempty) :
    (∑ i ∈ g₁, p.a i) * (1 - ∑ i ∈ g₂, p.rho i) + (∑ i ∈ g₂, p.a i) * (1 - ∑ i ∈ g₁, p.rho i)
        - (∑ i ∈ g₁ ∩ g₂, p.a i) * (1 - ∑ i ∈ g₁ ∪ g₂, p.rho i) <
      (∑ i ∈ g₁ ∪ g₂, p.a i) * (1 - ∑ i ∈ g₁ ∩ g₂, p.rho i) := by
  have rho_pos : ∀ i, 0 < p.rho i := fun i => div_pos (p.lam_pos i) (p.mu_pos i)
  have a_pos : ∀ i, 0 < p.a i := fun i => div_pos (rho_pos i) (p.mu_pos i)
  have hA1 : 0 < ∑ i ∈ g₁ \ g₂, p.a i := Finset.sum_pos (fun i _ => a_pos i) h₁
  have hA2 : 0 < ∑ i ∈ g₂ \ g₁, p.a i := Finset.sum_pos (fun i _ => a_pos i) h₂
  have hR1 : 0 < ∑ i ∈ g₁ \ g₂, p.rho i := Finset.sum_pos (fun i _ => rho_pos i) h₁
  have hR2 : 0 < ∑ i ∈ g₂ \ g₁, p.rho i := Finset.sum_pos (fun i _ => rho_pos i) h₂
  have e1a := Finset.sum_inter_add_sum_sdiff g₁ g₂ p.a
  have e2a := Finset.sum_inter_add_sum_sdiff g₂ g₁ p.a
  have e1r := Finset.sum_inter_add_sum_sdiff g₁ g₂ p.rho
  have e2r := Finset.sum_inter_add_sum_sdiff g₂ g₁ p.rho
  have eua := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := p.a)
  have eur := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := p.rho)
  rw [Finset.inter_comm g₂ g₁] at e2a e2r
  have s1a : ∑ i ∈ g₁, p.a i = ∑ i ∈ g₁ ∩ g₂, p.a i + ∑ i ∈ g₁ \ g₂, p.a i := e1a.symm
  have s2a : ∑ i ∈ g₂, p.a i = ∑ i ∈ g₁ ∩ g₂, p.a i + ∑ i ∈ g₂ \ g₁, p.a i := e2a.symm
  have s1r : ∑ i ∈ g₁, p.rho i = ∑ i ∈ g₁ ∩ g₂, p.rho i + ∑ i ∈ g₁ \ g₂, p.rho i := e1r.symm
  have s2r : ∑ i ∈ g₂, p.rho i = ∑ i ∈ g₁ ∩ g₂, p.rho i + ∑ i ∈ g₂ \ g₁, p.rho i := e2r.symm
  have sua : ∑ i ∈ g₁ ∪ g₂, p.a i = ∑ i ∈ g₁ ∩ g₂, p.a i + ∑ i ∈ g₁ \ g₂, p.a i
      + ∑ i ∈ g₂ \ g₁, p.a i := by linarith
  have sur : ∑ i ∈ g₁ ∪ g₂, p.rho i = ∑ i ∈ g₁ ∩ g₂, p.rho i + ∑ i ∈ g₁ \ g₂, p.rho i
      + ∑ i ∈ g₂ \ g₁, p.rho i := by linarith
  rw [s1a, s2a, s1r, s2r, sua, sur]
  have key := mul_pos hA1 hR2
  have key2 := mul_pos hA2 hR1
  nlinarith [key, key2]

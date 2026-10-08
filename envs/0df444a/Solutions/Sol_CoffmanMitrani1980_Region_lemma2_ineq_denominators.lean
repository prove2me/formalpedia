-- Prove2me | solution 1 for CoffmanMitrani1980.Region.lemma2_ineq_denominators
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T16:05:32.817989+00:00
-- url     : https://prove2.me/submissions/99e1a287-5615-4c17-b8c6-c56afedb37db

import Mathlib
import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

open CoffmanMitrani1980.Region in
theorem solution {M : ℕ} (p : Params M) (g₁ g₂ : Finset (Fin M))
    (h₁ : (g₁ \ g₂).Nonempty) (h₂ : (g₂ \ g₁).Nonempty) :
    (1 - ∑ i ∈ g₁ ∪ g₂, p.rho i) * (1 - ∑ i ∈ g₁ ∩ g₂, p.rho i) <
      (1 - ∑ i ∈ g₁, p.rho i) * (1 - ∑ i ∈ g₂, p.rho i) := by
  have hpos : ∀ i, 0 < p.rho i := fun i => div_pos (p.lam_pos i) (p.mu_pos i)
  have hA : 0 < ∑ i ∈ g₁ \ g₂, p.rho i := Finset.sum_pos (fun i _ => hpos i) h₁
  have hB : 0 < ∑ i ∈ g₂ \ g₁, p.rho i := Finset.sum_pos (fun i _ => hpos i) h₂
  have e1 := Finset.sum_inter_add_sum_sdiff g₁ g₂ p.rho
  have e2 := Finset.sum_inter_add_sum_sdiff g₂ g₁ p.rho
  have e3 := Finset.sum_union_inter (s₁ := g₁) (s₂ := g₂) (f := p.rho)
  rw [Finset.inter_comm g₂ g₁] at e2
  generalize ∑ i ∈ g₁ ∪ g₂, p.rho i = U at e3 ⊢
  generalize ∑ i ∈ g₁ ∩ g₂, p.rho i = C at e1 e2 e3 ⊢
  generalize ∑ i ∈ g₁ \ g₂, p.rho i = A at hA e1 ⊢
  generalize ∑ i ∈ g₂ \ g₁, p.rho i = B at hB e2 ⊢
  generalize ∑ i ∈ g₁, p.rho i = S₁ at e1 e3 ⊢
  generalize ∑ i ∈ g₂, p.rho i = S₂ at e2 e3 ⊢
  have hU : U = C + A + B := by linarith
  subst hU e1 e2
  have key : (1 - (C + A)) * (1 - (C + B)) - (1 - (C + A + B)) * (1 - C) = A * B := by ring
  have hAB : 0 < A * B := mul_pos hA hB
  linarith

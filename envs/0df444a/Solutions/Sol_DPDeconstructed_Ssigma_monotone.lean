-- Prove2me | solution 1 for DPDeconstructed.Ssigma_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:44:07.621212+00:00
-- url     : https://prove2.me/submissions/e3cfca9b-820d-4bf0-bf65-5c70b4e3ab46

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization

open DPDeconstructed DPDeconstructed.DynProg DPDeconstructed.PlanFactorization in
theorem solution {X A : Type*} [Nonempty X] (D : DynProg X A)
    (P : PlanFactorization D) (hW₀ : MonotoneOn P.W₀ D.𝒱) (hW₁ : MonotoneOn P.W₁ P.calG)
    (σ : D.Policy) :
    MonotoneOn (P.Sσ σ) P.calG := by
  intro g hg g' hg' hle
  obtain ⟨v, hv, rfl⟩ := hg
  obtain ⟨v', hv', rfl⟩ := hg'
  have mem : ∀ u ∈ D.𝒱, D.Mσ σ (P.W₁ (P.W₀ u)) ∈ D.𝒱 := by
    intro u hu
    obtain ⟨w, hw, hwx⟩ := σ.2.2 u hu
    have heq : D.Mσ σ (P.W₁ (P.W₀ u)) = w := by
      funext x
      have h1 := P.factor u hu ⟨(x, σ.1 x), σ.2.1 x⟩
      have h2 := hwx x
      apply EReal.coe_injective
      rw [h2]
      exact h1
    rw [heq]
    exact hw
  have hW1le : P.W₁ (P.W₀ v) ≤ P.W₁ (P.W₀ v') := hW₁ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩ hle
  show P.W₀ (D.Mσ σ (P.W₁ (P.W₀ v))) ≤ P.W₀ (D.Mσ σ (P.W₁ (P.W₀ v')))
  exact hW₀ (mem v hv) (mem v' hv') (fun x => hW1le _)

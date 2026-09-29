-- Prove2me | solution 1 for GaloisRepAdic.isEquiv_of_charpoly_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2524992c-558c-5c28-89c2-4111ec646f99

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_GaloisRepAdic_isEquiv_of_residual_isAbsolutelyIrreducible_of_trace_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isEquiv_of_charpoly_frobenius_eq
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

theorem trace_eq_of_charpoly_eq {A : Type} [CommRing A] [IsLocalRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ)) : ρ₁.trace σ = ρ₂.trace σ := by
  classical

  have key : ∀ (ρ : GaloisRepAdic A), ρ.trace σ = -(LinearMap.charpoly (ρ.ρ σ)).nextCoeff := by
    intro ρ
    let b := Module.finBasisOfFinrankEq A ρ.V ρ.finrank_eq
    show LinearMap.trace A ρ.V (ρ.ρ σ) = _
    rw [LinearMap.trace_eq_matrix_trace A b, ← LinearMap.charpoly_toMatrix (ρ.ρ σ) b,
      Matrix.trace_eq_neg_charpoly_nextCoeff]
  rw [key ρ₁, key ρ₂, h]

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Finite (IsLocalRing.ResidueField A)]
    (ρ₁ ρ₂ : GaloisRepAdic A)
    (h₁ : ρ₁.residual.IsAbsolutelyIrreducible) (h₂ : ρ₂.residual.IsAbsolutelyIrreducible)
    (S : Finset ℕ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ)) :
    ρ₁.IsEquiv ρ₂ :=
  GaloisRepAdic.isEquiv_of_residual_isAbsolutelyIrreducible_of_trace_eq ρ₁ ρ₂ h₁ h₂ fun σ =>
    trace_eq_of_charpoly_eq ρ₁ ρ₂ σ
      (GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq ρ₁ ρ₂ S
        (fun ℓ hℓ hℓS B τ hB hτ => h ℓ hℓ hℓS B hB τ hτ) σ)

end S_GaloisRepAdic_isEquiv_of_charpoly_frobenius_eq
end P2MW
export P2MW.S_GaloisRepAdic_isEquiv_of_charpoly_frobenius_eq (solution)

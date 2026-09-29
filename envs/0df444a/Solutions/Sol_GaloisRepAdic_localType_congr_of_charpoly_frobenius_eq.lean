-- Prove2me | solution 1 for GaloisRepAdic.localType_congr_of_charpoly_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5e82fc1c-80f6-562d-9cfb-c3b828a65dd9

import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_localType_congr_of_charpoly_frobenius_eq
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ₁ ρ₂ : GaloisRepAdic A)
    (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime ℓ → B.IsFrobeniusAt τ ℓ →
        LinearMap.charpoly (ρ₁.ρ τ) = LinearMap.charpoly (ρ₂.ρ τ)) :
    (∀ q : ℕ, ρ₁.IsUnipotentOnInertiaAt q ↔ ρ₂.IsUnipotentOnInertiaAt q) ∧
    (∀ (q : ℕ) (B : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), B.LiesOverPrime q → B.IsFrobeniusAt τ q →
        LinearMap.charpoly (ρ₁.ρ τ) = LinearMap.charpoly (ρ₂.ρ τ)) := by
  have hall : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ) :=
    GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq ρ₁ ρ₂ S hfrob
  refine ⟨fun q => ?_, fun _ _ τ _ _ => hall τ⟩
  constructor
  · intro h P hP σ hσ
    rw [← hall σ]
    exact h P hP σ hσ
  · intro h P hP σ hσ
    rw [hall σ]
    exact h P hP σ hσ

end S_GaloisRepAdic_localType_congr_of_charpoly_frobenius_eq
end P2MW
export P2MW.S_GaloisRepAdic_localType_congr_of_charpoly_frobenius_eq (solution)

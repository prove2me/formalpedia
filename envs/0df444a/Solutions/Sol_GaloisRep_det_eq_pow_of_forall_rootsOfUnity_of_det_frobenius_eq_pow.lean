-- Prove2me | solution 1 for GaloisRep.det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/99b9449b-51e8-5b0b-8172-0e2091e96ffe

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_GaloisRep_det_eq_cycloChar_pow_of_det_frobenius_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite) (m : ℕ)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (hfin : GaloisFactorsThroughFiniteLevel ρ)
    (hdet : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          Matrix.det (ρ σ).val = (ℓ : F) ^ m)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
      (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) → Matrix.det (ρ σ).val = (a : F) ^ m := by
  classical
  intro σ _ a ha
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p := HasEnoughRootsOfUnity.prim
  set cyc := IsPrimitiveRoot.autToPow ℚ hζ with hcyc_def
  have hspec : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ζ = ζ ^ ((cyc τ : ZMod p)).val :=
    fun τ => (IsPrimitiveRoot.autToPow_spec ℚ hζ τ).symm
  have hcyc : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ p = 1 → τ μ = μ ^ ((cyc τ : ZMod p)).val := by
    intro τ μ hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    rw [map_pow, hspec τ, ← pow_mul, ← pow_mul, mul_comm]
  have hB := GaloisRep.det_eq_cycloChar_pow_of_det_frobenius_eq_pow p cyc hcyc N S hSfin m ρ hfin hdet σ

  have h1 : ζ ^ (a % p) = ζ ^ ((cyc σ : ZMod p)).val := by
    rw [← hspec σ, ha ζ hζ.pow_eq_one, ← pow_mod_orderOf ζ a, ← hζ.eq_orderOf]
  have h2 : a % p = ((cyc σ : ZMod p)).val :=
    hζ.pow_inj (Nat.mod_lt _ hp.pos) (ZMod.val_lt _) h1
  have h3 : ((cyc σ : ZMod p)) = (a : ZMod p) := by
    rw [← ZMod.natCast_zmod_val (cyc σ : ZMod p), ← h2, ZMod.natCast_mod]
  rw [hB, h3, map_natCast]

end S_GaloisRep_det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow
end P2MW
export P2MW.S_GaloisRep_det_eq_pow_of_forall_rootsOfUnity_of_det_frobenius_eq_pow (solution)

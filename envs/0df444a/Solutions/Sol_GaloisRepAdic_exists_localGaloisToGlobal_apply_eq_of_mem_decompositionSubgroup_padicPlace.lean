-- Prove2me | solution 1 for GaloisRepAdic.exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0ec7144e-e8f4-5077-987e-0db03b5743b8

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace

set_option autoImplicit false

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime] (ρ : GaloisRepAdic B)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ (padicPlace p).decompositionSubgroup ℚ) :
    ∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) = ρ.ρ σ := by

  obtain ⟨n, hn⟩ : IsNilpotent (IsLocalRing.maximalIdeal B) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal B) bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot

  obtain ⟨L, hL, hlev⟩ := ρ.isAdicContinuous n
  haveI : FiniteDimensional ℚ L := hL
  have hker : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ L.fixingSubgroup →
      ρ.ρ τ = 1 := by
    intro τ hτ
    refine LinearMap.ext fun v => ?_
    have h := hlev τ ((IntermediateField.mem_fixingSubgroup_iff L τ).mp hτ) v
    rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at h
    exact h

  have hcl : σ ∈ closure (Set.range (localGaloisToGlobal p)) := by
    have h :=
      ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal p hσ
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, MonoidHom.coe_range] at h
    exact h
  have hopen : IsOpen ((fun τ => σ⁻¹ * τ) ⁻¹'
      (L.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :=
    (IntermediateField.fixingSubgroup_isOpen L).preimage (continuous_const_mul σ⁻¹)
  have hmem : σ ∈ (fun τ => σ⁻¹ * τ) ⁻¹'
      (L.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
    show σ⁻¹ * σ ∈ (L.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    rw [inv_mul_cancel]
    exact one_mem _
  obtain ⟨_, hτo, g, rfl⟩ := (mem_closure_iff.mp hcl) _ hopen hmem
  refine ⟨g, ?_⟩
  have h1 : ρ.ρ (σ⁻¹ * localGaloisToGlobal p g) = 1 := hker _ hτo
  rw [← mul_inv_cancel_left σ (localGaloisToGlobal p g), map_mul, h1, mul_one]

end S_GaloisRepAdic_exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace
end P2MW
export P2MW.S_GaloisRepAdic_exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace (solution)

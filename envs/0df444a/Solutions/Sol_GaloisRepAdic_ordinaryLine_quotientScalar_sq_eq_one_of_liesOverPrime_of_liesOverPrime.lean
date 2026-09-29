-- Prove2me | solution 1 for GaloisRepAdic.ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/cf026086-8915-59fa-800d-7636a7459d97

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime)
    (P P' : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (hP' : P'.LiesOverPrime p)
    (h' : ∀ L' : Submodule A ρ.V, (∃ b : Module.Basis (Fin 2) A ρ.V, L' = A ∙ b 0) →
      (∀ σ ∈ P'.decompositionSubgroup ℚ, ∀ v ∈ L', ρ.ρ σ v ∈ L') →
      (∀ σ ∈ P'.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L') →
      ∀ σ ∈ P'.decompositionSubgroup ℚ, ∀ z : A,
        (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L') → z * z = 1)
    (L : Submodule A ρ.V) (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.decompositionSubgroup ℚ)
    (z : A) (hz : ∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) :
    z * z = 1 := by

  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp P P' hP hP'
  subst hg
  obtain ⟨b, hb⟩ := hLb

  have hinv1 : ∀ v : ρ.V, ρ.ρ g (ρ.ρ g⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hinv2 : ∀ v : ρ.V, ρ.ρ g⁻¹ (ρ.ρ g v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have key : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V),
      ρ.ρ g (ρ.ρ (g⁻¹ * τ * g) (ρ.ρ g⁻¹ v)) = ρ.ρ τ v := by
    intro τ v
    have h1 : ρ.ρ g * ρ.ρ (g⁻¹ * τ * g) * ρ.ρ g⁻¹ = ρ.ρ τ := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [← h1, Module.End.mul_apply, Module.End.mul_apply]

  let e : ρ.V ≃ₗ[A] ρ.V :=
    LinearEquiv.ofLinear (ρ.ρ g) (ρ.ρ g⁻¹) (LinearMap.ext hinv1) (LinearMap.ext hinv2)
  let L' : Submodule A ρ.V := L.map (ρ.ρ g)
  have hmemL' : ∀ w ∈ L, ρ.ρ g w ∈ L' := fun w hw => Submodule.mem_map_of_mem hw
  have hL'b : ∃ b' : Module.Basis (Fin 2) A ρ.V, L' = A ∙ b' 0 := by
    refine ⟨b.map e, ?_⟩
    rw [Module.Basis.map_apply, LinearEquiv.ofLinear_apply]
    show Submodule.map (ρ.ρ g) L = _
    rw [hb, Submodule.map_span, Set.image_singleton]

  have hD : ∀ τ ∈ (g • P).decompositionSubgroup ℚ, g⁻¹ * τ * g ∈ P.decompositionSubgroup ℚ := by
    intro τ hτ
    simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hτ ⊢
    rw [mul_smul, mul_smul, hτ, inv_smul_smul]
  have hI : ∀ τ ∈ (g • P).inertiaSubgroupIn ℚ, g⁻¹ * τ * g ∈ P.inertiaSubgroupIn ℚ :=
    fun τ hτ => ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul P g hτ

  have hL'D : ∀ τ ∈ (g • P).decompositionSubgroup ℚ, ∀ v ∈ L', ρ.ρ τ v ∈ L' := by
    intro τ hτ v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    rw [← key τ, hinv2]
    exact hmemL' _ (hLD _ (hD τ hτ) w hw)
  have hL'I : ∀ τ ∈ (g • P).inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L' := by
    intro τ hτ v
    have hmem := hmemL' _ (hLI _ (hI τ hτ) (ρ.ρ g⁻¹ v))
    rw [map_sub, hinv1] at hmem
    rw [← key τ v]
    exact hmem

  have hσ' : g * σ * g⁻¹ ∈ (g • P).decompositionSubgroup ℚ := by
    simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hσ ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, hσ]
  have hs : g⁻¹ * (g * σ * g⁻¹) * g = σ := by group
  have hz' : ∀ v : ρ.V, ρ.ρ (g * σ * g⁻¹) v - z • v ∈ L' := by
    intro v
    have hmem := hmemL' _ (hz (ρ.ρ g⁻¹ v))
    rw [map_sub, map_smul, hinv1] at hmem
    rw [← key (g * σ * g⁻¹) v, hs]
    exact hmem
  exact h' L' hL'b hL'D hL'I (g * σ * g⁻¹) hσ' z hz'

end S_GaloisRepAdic_ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime
end P2MW
export P2MW.S_GaloisRepAdic_ordinaryLine_quotientScalar_sq_eq_one_of_liesOverPrime_of_liesOverPrime (solution)

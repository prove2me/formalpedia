-- Prove2me | solution 1 for GaloisRep.DeformationRingData.length_cotangent_le_add_of_isUnipotentOnInertiaAt_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0a13c1cf-2850-5bf4-bd9c-8820d9a6f8fb

import Theorems.Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnipotentOnInertiaAt
import Theorems.Thm_GaloisRep_DeformationRingData_length_cotangent_le_of_level_bounds
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_frobConj
import Theorems.Thm_ValuationSubring_exists_tame_generator_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_isUnipotentOnInertiaAt_point

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (hx' : IsLocalHom (x₀.comp θ : D'.R →+* 𝒪))
    (hur : (D'.ρ.baseChangeAlong (x₀.comp θ : D'.R →+* 𝒪) hx').IsUnipotentOnInertiaAt q)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsUnipotentOnInertiaAt q → 𝒟₀ ρA) :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent +
        Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by
  obtain ⟨P, hP⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨q, hq⟩
  obtain ⟨σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq P hP
  refine GaloisRep.DeformationRingData.length_cotangent_le_of_level_bounds D₀ D' θ x₀ hθsurj _
    fun n => ?_
  refine GaloisRep.DeformationRingData.length_level_quotient_le_of_isUnipotentOnInertiaAt D₀ D' θ x₀
    hx₀ hθ hθρ hθsurj p q hp hq hpq hp𝔪 P hP σ
    (fun P' hP' => ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hq P P' hP hP')
    hx' hur Hdet H1 H2 ?_ ?_ n
  · intro k τ hτ
    obtain ⟨w, hw, hwk⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_frobConj hp hq hpq P hP σ hσ k τ hτ
    exact ⟨w, hw, hwk⟩
  · intro m
    exact ValuationSubring.exists_tame_generator_inertiaSubgroupIn hp hq hpq P hP m

end S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_isUnipotentOnInertiaAt_point
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_isUnipotentOnInertiaAt_point (solution)

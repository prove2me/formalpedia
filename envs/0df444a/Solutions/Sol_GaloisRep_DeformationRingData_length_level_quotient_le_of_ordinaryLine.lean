-- Prove2me | solution 1 for GaloisRep.DeformationRingData.length_level_quotient_le_of_ordinaryLine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e75a9902-352b-5386-8844-3b437e7d02ec

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.BilinearMap
import Theorems.Thm_Module_length_quotient_le_of_ker_le
import Theorems.Thm_IsDiscreteValuationRing_length_ker_lsmul_quotient_maximalIdeal_pow_le
import Theorems.Thm_GaloisRep_DeformationRingData_exists_localInvariant_of_ordinaryLine
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_ordinaryLine
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity AlgebraicClosure.Rat.isGalois instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false

open scoped Pointwise

namespace PRungL2

theorem length_quotient_span_zero_eq_top (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {(0 : 𝒪)}) = ⊤ := by

  rw [(Submodule.quotEquivOfEqBot (Ideal.span {(0 : 𝒪)}) (Ideal.span_singleton_eq_bot.mpr rfl)).length_eq]
  by_contra h
  have hfl : IsFiniteLength 𝒪 𝒪 := Module.length_ne_top_iff.mp h
  haveI : IsArtinianRing 𝒪 := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  exact IsDiscreteValuationRing.not_isField 𝒪 (IsArtinianRing.isField_of_isDomain 𝒪)

theorem length_quotient_le_of_killed_functional
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {H : Type} [AddCommGroup H] [Module 𝒪 H] (K : Submodule 𝒪 H) (a : 𝒪) (n : ℕ)
    (y : H →ₗ[𝒪] 𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪 ^ (n + 1))
    (hy : ∀ h, a • y h = 0) (hK : ∀ h, y h = 0 → h ∈ K) :
    Module.length 𝒪 (H ⧸ K) ≤ Module.length 𝒪 (𝒪 ⧸ Ideal.span {a}) := by
  let T := LinearMap.ker (LinearMap.lsmul 𝒪 (𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪 ^ (n + 1)) a)
  have hyT : ∀ h, y h ∈ T := fun h => by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply]
    exact hy h
  have hker : LinearMap.ker (y.codRestrict T hyT) ≤ K := fun h hh => hK h (by
    rw [LinearMap.mem_ker] at hh
    exact congrArg Subtype.val hh)
  exact (Module.length_quotient_le_of_ker_le K (y.codRestrict T hyT) hker).trans
    (IsDiscreteValuationRing.length_ker_lsmul_quotient_maximalIdeal_pow_le a n)

end PRungL2

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hfl : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsFlatAt p)
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (L : Submodule 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V)
    (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V, L = 𝒪 ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - v ∈ L)
    (α : 𝒪)
    (hα : ∀ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p →
      ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
        (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - α • v ∈ L)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (Hord : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsOrdinaryAt p)
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsFlatAt p → 𝒟₀ ρA)
    (n : ℕ) :
    Module.length 𝒪 (((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) ⧸
      LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype)) ≤
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {α ^ 2 - 1}) := by
  by_cases hα1 : α ^ 2 - 1 = 0
  ·
    rw [hα1, PRungL2.length_quotient_span_zero_eq_top]
    exact le_top
  · obtain ⟨y, hy, hK⟩ := GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine D₀ D' θ x₀ p hp hp2
      hp𝔪 hθ hx₀ hfl hθρ hθsurj P hP L hLb hLD hLI α hα Hdet H1 Hord H2 hα1 n
    exact PRungL2.length_quotient_le_of_killed_functional _ (α ^ 2 - 1) n y hy hK

end S_GaloisRep_DeformationRingData_length_level_quotient_le_of_ordinaryLine
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_ordinaryLine (solution)

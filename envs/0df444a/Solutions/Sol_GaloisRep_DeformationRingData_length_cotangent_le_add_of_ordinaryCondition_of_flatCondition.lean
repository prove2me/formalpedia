-- Prove2me | solution 1 for GaloisRep.DeformationRingData.length_cotangent_le_add_of_ordinaryCondition_of_flatCondition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9c9dd533-f0ea-5133-bf8e-1c1396e94481

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Theorems.Thm_GaloisRep_DeformationRingData_length_cotangent_le_of_level_bounds
import Theorems.Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_ordinaryLine
import Theorems.Thm_GaloisRepAdic_ordinaryCondition_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_ordinaryCondition_of_flatCondition
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity AlgebraicClosure.Rat.isGalois instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false

open scoped Pointwise

namespace PRungL1

open GaloisRep GaloisRepAdic

variable (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ)

theorem Hdet_ord {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A)
    (h : ordinaryCondition 𝒪 p S ρ) : ρ.DetIsCyclotomic p := h.1

theorem Hord_ord {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A)
    (h : ordinaryCondition 𝒪 p S ρ) : ρ.IsOrdinaryAt p := h.2.1

theorem H1_ord {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A)
    {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f)
    (h : ordinaryCondition 𝒪 p S ρ) : ordinaryCondition 𝒪 p S (ρ.baseChangeAlong f hf) :=
  GaloisRepAdic.ordinaryCondition_baseChangeAlong 𝒪 f hf ρ h

theorem H2_ord {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A)
    (h : ordinaryCondition 𝒪 p S ρ) (hfl : ρ.IsFlatAt p) : flatCondition 𝒪 p S ρ :=
  ⟨h.1, hfl, h.2.2⟩

end PRungL1

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (S : Finset ℕ) (hpS : p ∈ S)
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar (GaloisRep.flatCondition 𝒪 p S))
    (D' : GaloisRep.DeformationRingData 𝒪 ρbar (GaloisRep.ordinaryCondition 𝒪 p S))
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
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
        (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - α • v ∈ L) :
    Module.length 𝒪 (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent ≤
      Module.length 𝒪 (RingHom.ker x₀).Cotangent +
        Module.length 𝒪 (𝒪 ⧸ Ideal.span {α ^ 2 - 1}) := by
  have _ := hpS

  haveI : Finite (IsLocalRing.ResidueField 𝒪) := by
    haveI : Finite (IsLocalRing.ResidueField D₀.R) := D₀.isOfType.2.1.1
    haveI := hx₀
    refine Finite.of_surjective (IsLocalRing.ResidueField.map (x₀ : D₀.R →+* 𝒪)) fun y => ?_
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨IsLocalRing.residue D₀.R (algebraMap 𝒪 D₀.R t), ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    show IsLocalRing.residue 𝒪 (x₀ (algebraMap 𝒪 D₀.R t)) = IsLocalRing.residue 𝒪 t
    rw [x₀.commutes]
    rfl

  have hfl : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsFlatAt p :=
    GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField _ hx₀ D₀.ρ D₀.isOfType.2.1
  exact GaloisRep.DeformationRingData.length_cotangent_le_of_level_bounds D₀ D' θ x₀ hθsurj _
    (fun n => GaloisRep.DeformationRingData.length_level_quotient_le_of_ordinaryLine
      D₀ D' θ x₀ p hp hp2 hp𝔪 hθ hx₀ hfl hθρ hθsurj P hP L hLb hLD hLI α hα
      (PRungL1.Hdet_ord 𝒪 p S) (PRungL1.H1_ord 𝒪 p S) (PRungL1.Hord_ord 𝒪 p S) (PRungL1.H2_ord 𝒪 p S) n)

end S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_ordinaryCondition_of_flatCondition
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_ordinaryCondition_of_flatCondition (solution)

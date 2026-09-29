-- Prove2me | solution 1 for GaloisRep.nonempty_deformationRingData_ordinaryCondition_and_isUnipotentOnInertiaAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0c6558dc-3eca-53d4-85ff-526aa640b088

import Theorems.Thm_GaloisRep_nonempty_deformationRingData
import Theorems.Thm_GaloisRep_isDeformationCondition_ordinaryCondition
import Theorems.Thm_GaloisRep_tangentFinite_of_imp
import Theorems.Thm_GaloisRep_tangentFinite_ordinaryCondition
import Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_forall_quotient
import Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_isEquiv
import Theorems.Thm_GaloisRepAdic_isUnipotentOnInertiaAt_of_jointly_injective
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_nonempty_deformationRingData_ordinaryCondition_and_isUnipotentOnInertiaAt
p2m_attr_erase "instance" "Deformation.ProartinianCat.instCategory Deformation.ProartinianCat.topologicalSpace Deformation.ProartinianCat.instUniqueHomSelf Deformation.IsLocalProartinianAlgebra.toIsLocalHom Deformation.ProartinianCat.instDiscreteTopologyCarrierResidueField Deformation.ProartinianCat.algebra Deformation.IsLocalProartinianAlgebra.toIsLocalRing Deformation.IsLocalProartinianAlgebra.toIsProartinian Deformation.IsLocalProartinianAlgebra.toIsTopologicalRing Deformation.ProartinianCat.instCoeSortType Deformation.ProartinianCat.instUniqueHomResidueField Deformation.ProartinianCat.instIsLocalHomCarrierContinuousAlgHomHom Deformation.IsLocalProartinianAlgebra.toIsResidueAlgebra Deformation.ProartinianCat.isLocalProartinianAlgebra Deformation.ProartinianCat.instIsAdicTopologyCarrierSelf Deformation.ProartinianCat.commRing Deformation.ProartinianCat.instFieldCarrierResidueField IsLocalRing.instDiscreteTopologyQuotientIdealHPowNatMaximalIdeal_definitions IsLocalRing.instIsLinearTopology_definitions IsProartinian.toT0Space instIsProartinianOfDiscreteTopologyOfIsArtinianRing IsLocalRing.instIsAdicTopology instIsProartinianOfIsAdicTopologyOfIsNoetherianRingOfCompactSpace IsLocalRing.instIsHausdorffMaximalIdealOfIsNoetherianRing_definitions IsLocalRing.instNonarchimedeanRing_definitions IsLocalRing.instIsPrecompleteMaximalIdealOfCompactSpace_definitions IsLocalRing.instDiscreteTopologyOfIsArtinianRing_definitions IsLocalRing.instT2SpaceOfIsNoetherianRing_definitions IsProartinian.toCompleteSpace IsProartinian.toIsLinearTopology instTopologicallyFGOfFiniteType instMulSemiringActionSubtypeMemIntermediateFieldOfSMulCommClassOfNormal_definitions instIsLocalHomRingHomAlgebraMap_definitions instContinuousConstSMulConjActOfContinuousMul_definitions instIsLocalHomRingHomToRingHom_definitions_1 instIsLocalHomResidueFieldRingHomAlgebraMap_definitions instMulSemiringActionRingOfIntegers_definitions instIsLocalHomRingHomToRingHom_definitions instMulActionContinuousMonoidHomOfContinuousConstSMul_definitions instFiniteIndexMulOppositeOp_definitions"
p2m_attr_erase "instance" "ValuationSubring.smulCommClass instFaithfulSMulSubtypeMemValuationSubring_definitions ContinuousAlgHom.isLocalHom_id instIsModuleTopologyMatrixOfFiniteOfIsTopologicalRing_definitions IsTopologicalAddGroup.discreteUniformity IntermediateField.smulCommClass_of_normal instMulActionMonoidHomOfMulDistribMulAction_definitions IsTopologicalGroup.discreteUniformity instIsLocalHomRingHomOfContinuousAlgHom_definitions Additive.instDistrbMulAction instIsLocalHomRingHomOfContinuousAlgHom_definitions_1 instNumberFieldSubtypeMemIntermediateFieldOfFiniteDimensional_definitions ContinuousAlgHom.isLocalHom_comp instIsLocalHomContinuousAlgHomToContinuousAlgHom_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsResidueAlgebra.inst"
p2m_attr_erase "instance" "IsResidueAlgebra.instQuotientIdeal IsLocalRing.quot IsLocalHom.quotient_mk Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace Deformation.ProartinianCat.ClosedSubalgebra.instNontrivialSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsLinearTopologySubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsTopologicalRingSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.instIsResidueAlgebraDualNumberResidueField Deformation.ProartinianCat.instDiscreteTopologyCarrierDualNumbers Deformation.ProartinianCat.instTopologicalSpaceDualNumberResidueField Deformation.ProartinianCat.instDiscreteTopologyDualNumberResidueField Deformation.ProartinianCat.instIsArtinianRingDualNumberResidueField Deformation.ProartinianCat.instFiniteResidueFieldDualNumber Deformation.ProartinianCat.instIsLocalHomDualNumberResidueFieldRingHomAlgebraMap Deformation.ProartinianCat.instIsLocalProartinianAlgebraDualNumberResidueField"
p2m_attr_erase "simp" "GaloisRep.conditionSubfunctor_obj Deformation.mapRepn_apply Deformation.repnFunctor_map Deformation.ProartinianCat.Hom.mk.injEq Deformation.ProartinianCat.ofHom_comp Deformation.ProartinianCat.hom_comp Deformation.ProartinianCat.mk.sizeOf_spec Deformation.ProartinianCat.Hom.mk.sizeOf_spec Deformation.ProartinianCat.ofEquiv_hom_hom Deformation.ProartinianCat.ofHom_id Deformation.ProartinianCat.hom_id Deformation.ProartinianCat.ofEquiv_inv_hom Deformation.ProartinianCat.mk.injEq Deformation.ProartinianCat.ofHom_hom ContinuousMonoidHom.val_inv_toHomUnits_toFun Units.val_mapₜ_toFun MonoidHom.coe_smul ContinuousAlgHom.coe_toContinuousMonoidHom ContinuousMonoidHom.val_toHomUnits_toFun ContinuousMonoidHom.mk_toMonoidHom ContinuousAlgHom.mapMatrix_apply Units.val_inv_mapₜ_toFun Units.coeHomₜ_toFun ContinuousMonoidHom.coe_mk ContinuousMonoidHom.coe_smul AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom Deformation.ProartinianCat.mem_tangentSubmodule Deformation.matrixRepresentation_apply Deformation.ProartinianCat.closedSubalgebraι_apply CategoryTheory.Functor.corepresentableByOfIsInitial_homEquiv_symm_apply CategoryTheory.Functor.representableByOfIsInitial_homEquiv_symm_apply CategoryTheory.Functor.corepresentableByOfIsInitial_homEquiv_apply CategoryTheory.Functor.representableByOfIsInitial_homEquiv_apply"

set_option autoImplicit false

namespace K2rEngine

open IsLocalRing

variable (𝒪 : Type) [CommRing 𝒪]

theorem isDeformationCondition_and
    (𝒟₁ 𝒟₂ : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h₁ : GaloisRep.IsDeformationCondition 𝒪 𝒟₁) (h₂ : GaloisRep.IsDeformationCondition 𝒪 𝒟₂) :
    GaloisRep.IsDeformationCondition 𝒪 (fun _A _ _ _ ρ => 𝒟₁ ρ ∧ 𝒟₂ ρ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A _ _ _ hA ρ ρ' e h
    exact ⟨h₁.of_isEquiv hA e h.1, h₂.of_isEquiv hA e h.2⟩
  · intro A B _ _ _ _ _ _ hA hB φ hφ ρ h
    exact ⟨h₁.baseChangeAlong hA hB φ hφ h.1, h₂.baseChangeAlong hA hB φ hφ h.2⟩
  · intro A B _ _ _ _ _ _ hA hB φ hφ hinj ρ h
    exact ⟨h₁.of_baseChangeAlong_injective hA hB φ hφ hinj h.1,
      h₂.of_baseChangeAlong_injective hA hB φ hφ hinj h.2⟩
  · intro A B C P _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC hP f g pA pB hpA hpB hfg hinj hsurj ρ hρA hρB
    exact ⟨h₁.of_fibreProduct hA hB hC hP f g pA pB hpA hpB hfg hinj hsurj hρA.1 hρB.1,
      h₂.of_fibreProduct hA hB hC hP f g pA pB hpA hpB hfg hinj hsurj hρA.2 hρB.2⟩
  · intro A _ _ _ _ _ hloc hres ρ
    constructor
    · rintro ⟨hρ₁, hρ₂⟩ B _ _ _ hB q hq hqs
      exact ⟨(h₁.iff_forall_surjective hloc hres ρ).mp hρ₁ hB q hq hqs,
        (h₂.iff_forall_surjective hloc hres ρ).mp hρ₂ hB q hq hqs⟩
    · intro H
      exact ⟨(h₁.iff_forall_surjective hloc hres ρ).mpr fun B _ _ _ hB q hq hqs => (H hB q hq hqs).1,
        (h₂.iff_forall_surjective hloc hres ρ).mpr fun B _ _ _ hB q hq hqs => (H hB q hq hqs).2⟩

theorem isArtinianTestAlgebra_quotient_pow
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra 𝒪 A]
    (hloc : IsLocalHom (algebraMap 𝒪 A))
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A)) (m : ℕ) :
    haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
        (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
    haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    GaloisRep.IsArtinianTestAlgebra 𝒪 (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) := by
  set I : Ideal A := IsLocalRing.maximalIdeal A ^ (m + 1) with hI
  have hItop : I ≠ ⊤ :=
    ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m))
  haveI hnt : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI hlq : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI hmk : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI := hloc
  refine ⟨?_, ?_, ?_⟩
  ·
    show IsLocalHom ((Ideal.Quotient.mk I).comp (algebraMap 𝒪 A))
    infer_instance
  ·
    intro y
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨o, ho⟩ := hres (IsLocalRing.residue A a)
    refine ⟨o, ?_⟩
    simp only [Function.comp_apply] at ho ⊢
    rw [← Ideal.Quotient.mk_algebraMap, ← sub_eq_zero, ← map_sub, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    have h1 : algebraMap 𝒪 A o - a ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact ho
    exact map_nonunit (Ideal.Quotient.mk I) _ h1
  ·
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    have hmax : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) =
        IsLocalRing.maximalIdeal (A ⧸ I) := by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hItop)]
    refine ⟨m + 1, ?_⟩
    rw [← hmax, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

theorem isDeformationCondition_unipotent (p : ℕ) (U : Finset ℕ) :
    GaloisRep.IsDeformationCondition 𝒪
      (fun _A _ _ _ ρ => ∀ q ∈ U, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A _ _ _ _ ρ ρ' e h q hq hqp hne
    exact GaloisRepAdic.isUnipotentOnInertiaAt_of_isEquiv e (h q hq hqp hne)
  · intro A B _ _ _ _ _ _ _ _ φ hφ ρ h q hq hqp hne
    exact GaloisRepAdic.isUnipotentOnInertiaAt_baseChangeAlong _ hφ ρ (h q hq hqp hne)
  · intro A B _ _ _ _ _ _ _ _ φ hφ hinj ρ h q hq hqp hne
    refine GaloisRepAdic.isUnipotentOnInertiaAt_of_jointly_injective (φ : A →+* B) hφ (φ : A →+* B)
      hφ ?_ ρ (h q hq hqp hne) (h q hq hqp hne)
    intro x hx _
    apply hinj
    rw [map_zero]
    exact hx
  · intro A B C P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g pA pB hpA hpB hfg hinj hsurj ρ hA hB q hq hqp hne
    refine GaloisRepAdic.isUnipotentOnInertiaAt_of_jointly_injective _ hpA _ hpB ?_ ρ
      (hA q hq hqp hne) (hB q hq hqp hne)
    intro x hx hy
    apply hinj
    show (pA x, pB x) = (pA 0, pB 0)
    rw [map_zero, map_zero]
    exact Prod.ext hx hy
  · intro A _ _ _ _ _ hloc hres ρ
    constructor
    · intro h B _ _ _ _ π hπ _ q hq hqp hne
      exact GaloisRepAdic.isUnipotentOnInertiaAt_baseChangeAlong _ hπ ρ (h q hq hqp hne)
    · intro H q hq hqp hne
      apply GaloisRepAdic.isUnipotentOnInertiaAt_of_forall_quotient ρ
      intro m
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      have hart := isArtinianTestAlgebra_quotient_pow 𝒪 hloc hres m
      exact H hart (Ideal.Quotient.mkₐ 𝒪 _)
        (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)
        (Ideal.Quotient.mkₐ_surjective 𝒪 _) q hq hqp hne

end K2rEngine

open K2rEngine in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (S U : Finset ℕ)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hbar : GaloisRep.ordinaryCondition 𝒪 p S (GaloisRepAdic.ofResidualGaloisRep ρbar))
    (hbarU : ∀ q ∈ U, q.Prime → q ≠ p →
      (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q) :
    Nonempty (GaloisRep.DeformationRingData 𝒪 ρbar
      (fun _A _ _ _ ρ => GaloisRep.ordinaryCondition 𝒪 p S ρ ∧
        ∀ q ∈ U, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q)) :=
  GaloisRep.nonempty_deformationRingData 𝒪 ρbar _ habs
    (isDeformationCondition_and 𝒪 (GaloisRep.ordinaryCondition 𝒪 p S)
      (fun _A _ _ _ ρ => ∀ q ∈ U, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q)
      (GaloisRep.isDeformationCondition_ordinaryCondition 𝒪 hp hp2)
      (isDeformationCondition_unipotent 𝒪 p U))
    ⟨hbar, hbarU⟩
    (GaloisRep.tangentFinite_of_imp 𝒪 ρbar _ (GaloisRep.ordinaryCondition 𝒪 p S)
      (fun _A _ _ _ _ρ h => h.1) (GaloisRep.tangentFinite_ordinaryCondition 𝒪 ρbar p S))

end S_GaloisRep_nonempty_deformationRingData_ordinaryCondition_and_isUnipotentOnInertiaAt
end P2MW
export P2MW.S_GaloisRep_nonempty_deformationRingData_ordinaryCondition_and_isUnipotentOnInertiaAt (solution)

-- Prove2me | solution 1 for CuspForm.TWLevel.exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9ef45cd3-96be-5cfa-9409-22bc5b699e80

import Mathlib
import Definitions.Def_CuspForm_TWLevelHeckeRing
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH
import Theorems.Thm_CohCarrier_heckeT_mem_parabolicHoms
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
import Theorems.Thm_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_RibetIrr_module_finite_padicInt_of_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH
p2m_attr_erase "instance" "CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite"
p2m_attr_erase "instance" "ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par CohCarrier.GammaHLower_finiteIndex AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace A2Comp

open Module

section Transport

variable {𝒪 : Type*} [CommRing 𝒪] {V W : Type*} [AddCommGroup V] [Module 𝒪 V]
  [AddCommGroup W] [Module 𝒪 W]
  (Vp : Submodule 𝒪 V) (Φ : V →ₗ[𝒪] Module.Dual 𝒪 W)
  (hs : Vp.map Φ = ⊤) (hi : ∀ v ∈ Vp, Φ v = 0 → v = 0)

include hs in
theorem exists_eq_of_dual (f : Module.Dual 𝒪 W) : ∃ v ∈ Vp, Φ v = f := by
  have : f ∈ Vp.map Φ := by rw [hs]; exact Submodule.mem_top
  exact Submodule.mem_map.mp this

variable [Module.Finite 𝒪 W] [Module.Free 𝒪 W]

include hs in

theorem eq_zero_of_forall (w : W) (h : ∀ v ∈ Vp, Φ v w = 0) : w = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff 𝒪 w).mp fun f => ?_
  obtain ⟨v, hv, rfl⟩ := exists_eq_of_dual Vp Φ hs f
  exact h v hv

include hs in
theorem eq_of_forall (w w' : W) (h : ∀ v ∈ Vp, Φ v w = Φ v w') : w = w' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall Vp Φ hs _ fun v hv => ?_
  rw [map_sub, h v hv, sub_self]

noncomputable def psi : Vp ≃ₗ[𝒪] Module.Dual 𝒪 W :=
  LinearEquiv.ofBijective (Φ.domRestrict Vp)
    ⟨fun x y hxy => by
        apply Subtype.ext
        have h : Φ ((x : V) - y) = 0 := by
          rw [map_sub]
          exact sub_eq_zero.mpr hxy
        exact sub_eq_zero.mp (hi _ (Vp.sub_mem x.2 y.2) h),
      fun f => by
        obtain ⟨v, hv, rfl⟩ := exists_eq_of_dual Vp Φ hs f
        exact ⟨⟨v, hv⟩, rfl⟩⟩

@[scoped simp] theorem psi_apply (v : Vp) : psi Vp Φ hs hi v = Φ v := rfl

theorem psi_symm_apply (v : V) (hv : v ∈ Vp) : (psi Vp Φ hs hi).symm (Φ v) = ⟨v, hv⟩ :=
  (psi Vp Φ hs hi).injective (by rw [LinearEquiv.apply_symm_apply, psi_apply])

noncomputable def rep : Module.Dual 𝒪 Vp ≃ₗ[𝒪] W :=
  (psi Vp Φ hs hi).symm.dualMap.trans (Module.evalEquiv 𝒪 W).symm

theorem rep_spec (y : Module.Dual 𝒪 Vp) (v : V) (hv : v ∈ Vp) :
    Φ v (rep Vp Φ hs hi y) = y ⟨v, hv⟩ := by
  show Φ v ((Module.evalEquiv 𝒪 W).symm ((psi Vp Φ hs hi).symm.dualMap y)) = _
  rw [Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply, psi_symm_apply Vp Φ hs hi v hv]

noncomputable def tr (a : Module.End 𝒪 V) : Module.End 𝒪 W :=
  (rep Vp Φ hs hi).toLinearMap ∘ₗ (Φ ∘ₗ a ∘ₗ Vp.subtype).flip

theorem tr_spec (a : Module.End 𝒪 V) (w : W) (v : V) (hv : v ∈ Vp) :
    Φ v (tr Vp Φ hs hi a w) = Φ (a v) w := by
  show Φ v (rep Vp Φ hs hi ((Φ ∘ₗ a ∘ₗ Vp.subtype).flip w)) = _
  rw [rep_spec Vp Φ hs hi _ v hv]
  rfl

include hs in

theorem eq_tr_of_adjoint (a : Module.End 𝒪 V) (b : Module.End 𝒪 W)
    (h : ∀ v ∈ Vp, Φ (a v) = Φ v ∘ₗ b) : b = tr Vp Φ hs hi a := by
  apply LinearMap.ext
  intro w
  refine eq_of_forall Vp Φ hs _ _ fun v hv => ?_
  rw [tr_spec Vp Φ hs hi a w v hv, h v hv]
  rfl

theorem tr_one : tr Vp Φ hs hi 1 = 1 :=
  (eq_tr_of_adjoint Vp Φ hs hi 1 1 fun v _ => LinearMap.ext fun w => rfl).symm

theorem tr_mul (a a' : Module.End 𝒪 V) (ha' : ∀ v ∈ Vp, a' v ∈ Vp) :
    tr Vp Φ hs hi (a * a') = tr Vp Φ hs hi a' * tr Vp Φ hs hi a := by
  symm
  refine eq_tr_of_adjoint Vp Φ hs hi _ _ fun v hv => ?_
  apply LinearMap.ext
  intro w
  rw [LinearMap.comp_apply, Module.End.mul_apply, Module.End.mul_apply, tr_spec Vp Φ hs hi a' _ v hv,
    tr_spec Vp Φ hs hi a _ (a' v) (ha' v hv)]

theorem tr_add (a a' : Module.End 𝒪 V) :
    tr Vp Φ hs hi (a + a') = tr Vp Φ hs hi a + tr Vp Φ hs hi a' := by
  symm
  refine eq_tr_of_adjoint Vp Φ hs hi _ _ fun v hv => ?_
  apply LinearMap.ext
  intro w
  rw [LinearMap.comp_apply, LinearMap.add_apply, map_add, LinearMap.add_apply, LinearMap.add_apply,
    map_add, tr_spec Vp Φ hs hi a _ v hv, tr_spec Vp Φ hs hi a' _ v hv]

theorem tr_smul (c : 𝒪) (a : Module.End 𝒪 V) :
    tr Vp Φ hs hi (c • a) = c • tr Vp Φ hs hi a := by
  symm
  refine eq_tr_of_adjoint Vp Φ hs hi _ _ fun v hv => ?_
  apply LinearMap.ext
  intro w
  rw [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply, map_smul, tr_spec Vp Φ hs hi a _ v hv]

theorem tr_algebraMap (c : 𝒪) :
    tr Vp Φ hs hi (algebraMap 𝒪 (Module.End 𝒪 V) c) = algebraMap 𝒪 (Module.End 𝒪 W) c := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, tr_smul, tr_one]

theorem tr_eq_zero_of_forall (a : Module.End 𝒪 V) (ha : ∀ v ∈ Vp, a v = 0) :
    tr Vp Φ hs hi a = 0 := by
  symm
  refine eq_tr_of_adjoint Vp Φ hs hi _ _ fun v hv => ?_
  rw [ha v hv, map_zero, LinearMap.comp_zero]

theorem tr_comm (a a' : Module.End 𝒪 V) (ha : ∀ v ∈ Vp, a v ∈ Vp) (ha' : ∀ v ∈ Vp, a' v ∈ Vp)
    (h : a * a' = a' * a) :
    tr Vp Φ hs hi a * tr Vp Φ hs hi a' = tr Vp Φ hs hi a' * tr Vp Φ hs hi a := by
  rw [← tr_mul Vp Φ hs hi a' a ha, ← tr_mul Vp Φ hs hi a a' ha', h]

theorem tr_comm_of_adjoint (a a' : Module.End 𝒪 V) (b : Module.End 𝒪 W)
    (hab : ∀ v ∈ Vp, Φ (a v) = Φ v ∘ₗ b) (ha : ∀ v ∈ Vp, a v ∈ Vp) (ha' : ∀ v ∈ Vp, a' v ∈ Vp)
    (h : a * a' = a' * a) :
    tr Vp Φ hs hi a' * b = b * tr Vp Φ hs hi a' := by
  rw [eq_tr_of_adjoint Vp Φ hs hi a b hab]
  exact (tr_comm Vp Φ hs hi a a' ha ha' h).symm

variable (a : Module.End 𝒪 V) (ha2 : a * a = a) (haVp : ∀ v, a v ∈ Vp)

abbrev corner : Submodule 𝒪 V := LinearMap.range a

theorem mem_corner_iff (u : V) : u ∈ corner a ↔ ∃ v, a v = u := LinearMap.mem_range

include ha2 in
theorem apply_eq_self_of_mem_corner {u : V} (hu : u ∈ corner a) : a u = u := by
  obtain ⟨v, rfl⟩ := (mem_corner_iff a _).mp hu
  show (a * a) v = a v
  rw [ha2]

include haVp in
theorem corner_le : corner a ≤ Vp := by
  rintro u ⟨v, rfl⟩
  exact haVp v

def toCornerVp : Vp →ₗ[𝒪] corner a := a.rangeRestrict ∘ₗ Vp.subtype

@[scoped simp] theorem coe_toCornerVp (v : Vp) : ((toCornerVp Vp a v : corner a) : V) = a v := rfl

noncomputable def Theta1 : Module.Dual 𝒪 (corner a) →ₗ[𝒪] W :=
  (rep Vp Φ hs hi).toLinearMap ∘ₗ (toCornerVp Vp a).dualMap

theorem Theta1_spec (y : Module.Dual 𝒪 (corner a)) (v : V) (hv : v ∈ Vp) :
    Φ v (Theta1 Vp Φ hs hi a y) = y ⟨a v, LinearMap.mem_range_self a v⟩ := by
  show Φ v (rep Vp Φ hs hi ((toCornerVp Vp a).dualMap y)) = _
  rw [rep_spec Vp Φ hs hi _ v hv]
  rfl

include ha2 haVp in
theorem Theta1_injective : Function.Injective (Theta1 Vp Φ hs hi a) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  apply LinearMap.ext
  intro u
  have hu : (u : V) ∈ Vp := corner_le Vp a haVp u.2
  have h := Theta1_spec Vp Φ hs hi a y u hu
  rw [hy, map_zero] at h
  have e : (⟨a u, LinearMap.mem_range_self a u⟩ : corner a) = u :=
    Subtype.ext (apply_eq_self_of_mem_corner a ha2 u.2)
  rw [e] at h
  exact h.symm

include ha2 haVp in

theorem range_Theta1 : LinearMap.range (Theta1 Vp Φ hs hi a) = LinearMap.range (tr Vp Φ hs hi a) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    refine ⟨Theta1 Vp Φ hs hi a y, ?_⟩
    refine eq_of_forall Vp Φ hs _ _ fun v hv => ?_
    rw [tr_spec Vp Φ hs hi a _ v hv, Theta1_spec Vp Φ hs hi a y v hv,
      Theta1_spec Vp Φ hs hi a y (a v) (haVp v)]
    congr 1
    apply Subtype.ext
    exact congrArg (fun f : Module.End 𝒪 V => f v) ha2
  · rintro _ ⟨w₀, rfl⟩

    let y : Module.Dual 𝒪 (corner a) := (LinearMap.applyₗ w₀ ∘ₗ Φ) ∘ₗ (corner a).subtype
    refine ⟨y, ?_⟩
    refine eq_of_forall Vp Φ hs _ _ fun v hv => ?_
    rw [Theta1_spec Vp Φ hs hi a y v hv, tr_spec Vp Φ hs hi a _ v hv]
    rfl

theorem corner_stable (a' : Module.End 𝒪 V) (h : a' * a = a * a') (u : V) (hu : u ∈ corner a) :
    a' u ∈ corner a := by
  obtain ⟨v, rfl⟩ := (mem_corner_iff a _).mp hu
  refine ⟨a' v, ?_⟩
  show (a * a') v = (a' * a) v
  rw [h]

def restrictCorner (a' : Module.End 𝒪 V) (h : a' * a = a * a') : Module.End 𝒪 (corner a) :=
  a'.restrict fun u hu => corner_stable a a' h u hu

@[scoped simp] theorem coe_restrictCorner (a' : Module.End 𝒪 V) (h : a' * a = a * a') (u : corner a) :
    ((restrictCorner a a' h u : corner a) : V) = a' u := rfl

include haVp in

theorem Theta1_comp (a' : Module.End 𝒪 V) (h : a' * a = a * a') (ha' : ∀ v ∈ Vp, a' v ∈ Vp)
    (y : Module.Dual 𝒪 (corner a)) :
    Theta1 Vp Φ hs hi a (y ∘ₗ restrictCorner a a' h) = tr Vp Φ hs hi a' (Theta1 Vp Φ hs hi a y) := by
  refine eq_of_forall Vp Φ hs _ _ fun v hv => ?_
  rw [Theta1_spec Vp Φ hs hi a _ v hv, tr_spec Vp Φ hs hi a' _ v hv,
    Theta1_spec Vp Φ hs hi a y (a' v) (ha' v hv), LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  exact congrArg (fun f : Module.End 𝒪 V => f v) h

include ha2 haVp in
theorem tr_idem : tr Vp Φ hs hi a * tr Vp Φ hs hi a = tr Vp Φ hs hi a := by
  rw [← tr_mul Vp Φ hs hi a a (fun v _ => haVp v), ha2]

omit [Module.Finite 𝒪 W] [Module.Free 𝒪 W] in

theorem aeval_stable {G : Type*} (op : G → Module.End 𝒪 V) (hstab : ∀ g, ∀ v ∈ Vp, op g v ∈ Vp)
    (ev : MvPolynomial G 𝒪 →ₐ[𝒪] Module.End 𝒪 V) (hev : ∀ g, ev (MvPolynomial.X g) = op g)
    (P : MvPolynomial G 𝒪) : ∀ v ∈ Vp, ev P v ∈ Vp := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro v hv
    have hC : ev (MvPolynomial.C c) = algebraMap 𝒪 _ c := ev.commutes c
    rw [hC, Module.algebraMap_end_apply]
    exact Vp.smul_mem c hv
  | add P Q hP hQ =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact Vp.add_mem (hP v hv) (hQ v hv)
  | mul_X P g hP =>
    intro v hv
    rw [map_mul, hev, Module.End.mul_apply]
    exact hP _ (hstab g v hv)

theorem tr_aeval_comm {G : Type*} (op : G → Module.End 𝒪 V) (hstab : ∀ g, ∀ v ∈ Vp, op g v ∈ Vp)
    (ev : MvPolynomial G 𝒪 →ₐ[𝒪] Module.End 𝒪 V) (hev : ∀ g, ev (MvPolynomial.X g) = op g)
    (b : Module.End 𝒪 W) (hb : ∀ g, tr Vp Φ hs hi (op g) * b = b * tr Vp Φ hs hi (op g))
    (P : MvPolynomial G 𝒪) : tr Vp Φ hs hi (ev P) * b = b * tr Vp Φ hs hi (ev P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hC : ev (MvPolynomial.C c) = algebraMap 𝒪 _ c := ev.commutes c
    rw [hC, tr_algebraMap]
    exact Algebra.commutes c b
  | add P Q hP hQ => rw [map_add, tr_add, add_mul, mul_add, hP, hQ]
  | mul_X P g hP =>
    rw [map_mul, hev, tr_mul Vp Φ hs hi _ _ (hstab g), mul_assoc, hP, ← mul_assoc, hb g, mul_assoc]

include ha2 haVp in

theorem package {M : Type*} [AddCommGroup M] [Module 𝒪 M] (ι : corner a ≃ₗ[𝒪] M)
    {I : Type*} (op : I → Module.End 𝒪 V) (gW : I → Module.End 𝒪 W) (gM : I → Module.End 𝒪 M)
    (hadj : ∀ i, ∀ v ∈ Vp, Φ (op i v) = Φ v ∘ₗ gW i)
    (hstab : ∀ i, ∀ v ∈ Vp, op i v ∈ Vp)
    (hcomm : ∀ i, op i * a = a * op i)
    (hιM : ∀ (i) (u : corner a), ι (restrictCorner a (op i) (hcomm i) u) = gM i (ι u))
    {G : Type*} (σW : G → Module.End 𝒪 W)
    (hσ : ∀ g, tr Vp Φ hs hi a * σW g = σW g * tr Vp Φ hs hi a) :
    ∃ E : W →ₗ[𝒪] W, E ∘ₗ E = E ∧ (∀ i, E ∘ₗ gW i = gW i ∘ₗ E) ∧ (∀ g, E ∘ₗ σW g = σW g ∘ₗ E) ∧
      ∃ Θ : Module.Dual 𝒪 M →ₗ[𝒪] W, Function.Injective Θ ∧
        LinearMap.range Θ = LinearMap.range E ∧
        ∀ (i) (y : Module.Dual 𝒪 M), Θ (y ∘ₗ gM i) = gW i (Θ y) := by
  refine ⟨tr Vp Φ hs hi a, tr_idem Vp Φ hs hi a ha2 haVp, fun i => ?_, fun g => hσ g,
    Theta1 Vp Φ hs hi a ∘ₗ ι.dualMap.toLinearMap, ?_, ?_, fun i y => ?_⟩
  · show tr Vp Φ hs hi a * gW i = gW i * tr Vp Φ hs hi a
    exact tr_comm_of_adjoint Vp Φ hs hi (op i) a (gW i) (hadj i) (hstab i) (fun v _ => haVp v)
      (hcomm i)
  · exact (Theta1_injective Vp Φ hs hi a ha2 haVp).comp ι.dualMap.injective
  · rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr ι.dualMap.surjective)]
    exact range_Theta1 Vp Φ hs hi a ha2 haVp
  · have h1 : ι.dualMap.toLinearMap (y ∘ₗ gM i) =
        (ι.dualMap.toLinearMap y) ∘ₗ restrictCorner a (op i) (hcomm i) := by
      apply LinearMap.ext
      intro u
      show y (gM i (ι u)) = y (ι (restrictCorner a (op i) (hcomm i) u))
      rw [hιM]
    rw [LinearMap.comp_apply, h1, Theta1_comp Vp Φ hs hi a haVp (op i) (hcomm i) (hstab i),
      eq_tr_of_adjoint Vp Φ hs hi (op i) (gW i) (hadj i)]
    rfl

end Transport

end A2Comp
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

namespace A2Comp

p2m_open "CohCarrier~rep"
open scoped IsMulCommutative

section LocCorner

variable {𝒪 : Type} [CommRing 𝒪] {V : Type} [AddCommGroup V] [Module 𝒪 V]
  {k : Type} [Field k] [Algebra 𝒪 k] (D : CohCarrier.HeckeData 𝒪 V k)

attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

def phiA : D.FreeAlg →ₐ[𝒪] ↥D.opSubalgebra :=
  MvPolynomial.aeval fun g =>
    (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ : ↥D.opSubalgebra)

theorem coe_phiA (P : D.FreeAlg) :
    ((phiA D P : ↥D.opSubalgebra) : Module.End 𝒪 V) = D.opAlgHom P := rfl

theorem smul_eq (P : D.FreeAlg) (v : V) : P • v = D.opAlgHom P v := rfl

theorem opSubalgebra_le_range : D.opSubalgebra ≤ D.opAlgHom.range :=
  Algebra.adjoin_le (by
    rintro _ ⟨g, rfl⟩
    exact ⟨MvPolynomial.X g, D.opAlgHom_X g⟩)

theorem phiA_surjective : Function.Surjective (phiA D) := by
  intro x
  obtain ⟨P, hP⟩ := opSubalgebra_le_range D x.2
  exact ⟨P, Subtype.ext hP⟩

theorem mTheta_isMaximal (hk : Function.Surjective (algebraMap 𝒪 k)) : D.mTheta.IsMaximal := by
  refine RingHom.ker_isMaximal_of_surjective D.thetaTilde.toRingHom fun x => ?_
  obtain ⟨c, rfl⟩ := hk x
  exact ⟨algebraMap 𝒪 D.FreeAlg c, D.thetaTilde.commutes c⟩

theorem toML_eq_mk (v : V) : D.toML v = LocalizedModule.mk v 1 := rfl

theorem thetaTilde_X_sub_C (g : D.Gen) (c : 𝒪) :
    D.thetaTilde (MvPolynomial.X g - MvPolynomial.C c) = D.θbar g - algebraMap 𝒪 k c := by
  rw [map_sub]
  show MvPolynomial.aeval D.θbar (MvPolynomial.X g) - MvPolynomial.aeval D.θbar (MvPolynomial.C c) = _
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_C]

theorem opAlgHom_X_sub_C_apply (g : D.Gen) (c : 𝒪) (w : V) :
    D.opAlgHom (MvPolynomial.X g - MvPolynomial.C c) w = D.op g w - c • w := by
  have hC : D.opAlgHom (MvPolynomial.C c) = algebraMap 𝒪 _ c := D.opAlgHom.commutes c
  rw [map_sub, HeckeData.opAlgHom_X, LinearMap.sub_apply, hC, Module.algebraMap_end_apply]

theorem toML_opAlgHom (P : D.FreeAlg) (v : V) : D.toML (D.opAlgHom P v) = P • D.toML v := by
  rw [← smul_eq]; exact D.toML.map_smul P v

theorem ML_eq_zero_of (s : D.FreeAlg) (hs : s ∉ D.mTheta) (hs0 : D.opAlgHom s = 0) (x : D.ML) :
    x = 0 := by
  induction x using LocalizedModule.induction_on with
  | h v t =>
    rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [smul_zero]
    rw [Submonoid.smul_def, smul_eq, hs0, LinearMap.zero_apply]

theorem exists_index (hk : Function.Surjective (algebraMap 𝒪 k))
    (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra)
    (hker : RingHom.ker (phiA D) ≤ D.mTheta) :
    ∃ i : Fin Sp.n, Ideal.comap (phiA D) (Sp.𝔪 i) = D.mTheta := by
  have hmax := mTheta_isMaximal D hk
  have hsurj := phiA_surjective D
  have hcm : Ideal.comap (phiA D) (Ideal.map (phiA D) D.mTheta) = D.mTheta := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, sup_eq_left]
    exact hker
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (phiA D) hsurj hmax with htop | hmax'
  · exfalso
    apply hmax.ne_top
    rw [← hcm, htop, Ideal.comap_top]
  · obtain ⟨i, hi⟩ := Sp.exists_eq _ hmax'
    exact ⟨i, by rw [hi, hcm]⟩

section Corner

variable (Sp : IharaLemma.IdempotentSplitting ↥D.opSubalgebra) (i₀ : Fin Sp.n)
  (hi₀ : Ideal.comap (phiA D) (Sp.𝔪 i₀) = D.mTheta)

def eEnd : Module.End 𝒪 V := (Sp.e i₀ : ↥D.opSubalgebra)

theorem eEnd_mul_eEnd : eEnd D Sp i₀ * eEnd D Sp i₀ = eEnd D Sp i₀ :=
  congrArg Subtype.val (Sp.idem i₀).eq

theorem opAlgHom_mul_eEnd (P : D.FreeAlg) :
    D.opAlgHom P * eEnd D Sp i₀ = eEnd D Sp i₀ * D.opAlgHom P :=
  congrArg Subtype.val (mul_comm (phiA D P) (Sp.e i₀))

theorem op_mul_eEnd (g : D.Gen) : D.op g * eEnd D Sp i₀ = eEnd D Sp i₀ * D.op g := by
  rw [← HeckeData.opAlgHom_X]; exact opAlgHom_mul_eEnd D Sp i₀ _

include hi₀ in
theorem phiA_notMem {s : D.FreeAlg} (hs : s ∉ D.mTheta) : phiA D s ∉ Sp.𝔪 i₀ := fun h =>
  hs (hi₀ ▸ (Ideal.mem_comap.mpr h))

include hi₀ in

theorem exists_inv (s : D.FreeAlg) (hs : s ∉ D.mTheta) :
    ∃ t : ↥D.opSubalgebra, t * phiA D s * Sp.e i₀ = Sp.e i₀ :=
  IharaLemma.exists_mul_mul_eq_of_notMem (Sp.idem i₀) (Sp.𝔪 i₀) (Sp.mem_of_isMaximal_of_ne i₀)
    (phiA_notMem D Sp i₀ hi₀ hs)

include hi₀ in

theorem exists_lift : ∃ c : D.FreeAlg, c ∉ D.mTheta ∧ D.opAlgHom c = eEnd D Sp i₀ := by
  obtain ⟨c, hc⟩ := phiA_surjective D (Sp.e i₀)
  refine ⟨c, fun hcm => Sp.notMem i₀ ?_, by rw [← coe_phiA, hc]; rfl⟩
  have : c ∈ Ideal.comap (phiA D) (Sp.𝔪 i₀) := by rw [hi₀]; exact hcm
  rwa [Ideal.mem_comap, hc] at this

include hi₀ in

theorem exists_opAlgHom_apply_eq (s : D.FreeAlg) (hs : s ∉ D.mTheta) (v : V) :
    ∃ w : V, D.opAlgHom s (eEnd D Sp i₀ w) = eEnd D Sp i₀ v := by
  obtain ⟨t, ht⟩ := exists_inv D Sp i₀ hi₀ s hs
  refine ⟨(t : Module.End 𝒪 V) v, ?_⟩
  have e1 : phiA D s * (Sp.e i₀ * t) = Sp.e i₀ :=
    calc phiA D s * (Sp.e i₀ * t) = t * phiA D s * Sp.e i₀ := by ring
      _ = Sp.e i₀ := ht
  exact congrArg (fun a : ↥D.opSubalgebra => (a : Module.End 𝒪 V) v) e1

abbrev cornerV : Submodule 𝒪 V := LinearMap.range (eEnd D Sp i₀)

theorem eEnd_apply_of_mem {u : V} (hu : u ∈ cornerV D Sp i₀) : eEnd D Sp i₀ u = u := by
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hu
  show (eEnd D Sp i₀ * eEnd D Sp i₀) v = _
  rw [eEnd_mul_eEnd]

def iota : cornerV D Sp i₀ →ₗ[𝒪] D.ML := D.toMLₒ ∘ₗ (cornerV D Sp i₀).subtype

theorem iota_apply (u : cornerV D Sp i₀) : iota D Sp i₀ u = D.toML u := rfl

include hi₀ in
theorem iota_injective : Function.Injective (iota D Sp i₀) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  rw [iota_apply, toML_eq_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hu
  obtain ⟨c, hc⟩ := hu
  simp only [smul_zero, Submonoid.smul_def, one_smul] at hc
  rw [smul_eq] at hc
  obtain ⟨t, ht⟩ := exists_inv D Sp i₀ hi₀ (c : D.FreeAlg) c.2
  apply Subtype.ext
  have h1 : ((t * phiA D c * Sp.e i₀ : ↥D.opSubalgebra) : Module.End 𝒪 V) u =
      (t : Module.End 𝒪 V) (D.opAlgHom c (eEnd D Sp i₀ u)) := rfl
  rw [ht, eEnd_apply_of_mem D Sp i₀ u.2, hc, map_zero] at h1
  rw [← eEnd_apply_of_mem D Sp i₀ u.2]
  exact h1

include hi₀ in
theorem iota_surjective : Function.Surjective (iota D Sp i₀) := by
  intro x
  induction x using LocalizedModule.induction_on with
  | h v s =>

    obtain ⟨w, key⟩ := exists_opAlgHom_apply_eq D Sp i₀ hi₀ (s : D.FreeAlg) s.2 v
    obtain ⟨c₀, hc₀, hc₀e⟩ := exists_lift D Sp i₀ hi₀
    refine ⟨⟨eEnd D Sp i₀ w, LinearMap.mem_range_self _ _⟩, ?_⟩
    rw [iota_apply, toML_eq_mk, LocalizedModule.mk_eq]
    refine ⟨⟨c₀, hc₀⟩, ?_⟩
    simp only [Submonoid.smul_def, one_smul]
    rw [smul_eq, smul_eq, smul_eq, hc₀e]
    show eEnd D Sp i₀ (D.opAlgHom s (eEnd D Sp i₀ w)) = eEnd D Sp i₀ v
    rw [key]
    show (eEnd D Sp i₀ * eEnd D Sp i₀) v = _
    rw [eEnd_mul_eEnd]

def iotaEquiv : cornerV D Sp i₀ ≃ₗ[𝒪] D.ML :=
  LinearEquiv.ofBijective (iota D Sp i₀) ⟨iota_injective D Sp i₀ hi₀, iota_surjective D Sp i₀ hi₀⟩

theorem iotaEquiv_apply (u : cornerV D Sp i₀) : iotaEquiv D Sp i₀ hi₀ u = D.toML u := rfl

end Corner
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

end LocCorner
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

end A2Comp
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

namespace A2Comp

section Concrete

p2m_open "CohCarrier~rep CongruenceSubgroup"
open scoped MatrixGroups

theorem trace_coe_conj' (g u : SL(2, ℤ)) :
    (((g * u * g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace =
      ((u : Matrix (Fin 2) (Fin 2) ℤ)).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem diamondRaw_isParabolicHom (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type*) [AddCommGroup A]
    (σ : Gamma0 M) (φ : H1 M H A) (hφ : ModularCurve.Period.IsParabolicHom (GammaH M H) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M H) (diamondRaw M H A σ φ) := by
  intro γ hγ
  show φ (Additive.ofMul (conjHom M H σ γ)) = 0
  apply hφ
  have : ((conjHom M H σ γ : ↥(GammaH M H)) : SL(2, ℤ)) =
      (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ := rfl
  rw [this, trace_coe_conj']
  exact hγ

theorem diamondL_mem_parabolicHoms (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (𝒪 : Type)
    [CommRing 𝒪] (d : (ZMod M)ˣ) (φ : H1 M H 𝒪)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪) :
    diamondL M H 𝒪 d φ ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪 :=
  diamondRaw_isParabolicHom M H 𝒪 _ φ hφ

theorem isTorsionFree_padicInt (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] 𝒪] : Module.IsTorsionFree ℤ_[p] 𝒪 := by
  have hinj : Function.Injective (algebraMap ℤ_[p] 𝒪) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    have hspec := PadicInt.unitCoeff_spec hne
    rw [hspec, map_mul, map_pow, map_natCast] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact (PadicInt.unitCoeff hne).isUnit.map (algebraMap ℤ_[p] 𝒪) |>.ne_zero h
    · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h
  refine Module.IsTorsionFree.of_smul_eq_zero fun a x hax => ?_
  rw [Algebra.smul_def] at hax
  rcases mul_eq_zero.mp hax with h | h
  · exact Or.inl (hinj (by rw [h, map_zero]))
  · exact Or.inr h

variable (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]

theorem tateGaloisRep_comp_tateGenOpH (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (g : CohCarrier.Gen L S) :
    ModularCurve.JH.tateGaloisRep L H p σ ∘ₗ ModularCurve.tateGenOpH L H S p g =
      ModularCurve.tateGenOpH L H S p g ∘ₗ ModularCurve.JH.tateGaloisRep L H p σ := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ModularCurve.JH.tateGaloisRep_apply_coe,
    ModularCurve.tateGenOpH_apply_coe, ModularCurve.tateGenOpH_apply_coe,
    ModularCurve.JH.tateGaloisRep_apply_coe]
  exact ModularCurve.galois_smul_genOpH_comm L H S σ g _

theorem baseChange_comp_comm {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A]
    {V : Type} [AddCommGroup V] [Module R V] {P Q : Module.End R V} (h : P ∘ₗ Q = Q ∘ₗ P) :
    (P.baseChange A) ∘ₗ (Q.baseChange A) = (Q.baseChange A) ∘ₗ (P.baseChange A) := by
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]

end Concrete
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

section Families

open CuspForm.TWLevel

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
  (H : Subgroup (ZMod (level N r qv))ˣ) [NeZero N] [NeZero r] [∀ i, NeZero (qv i)]
  (hq : ∀ i, (qv i).Prime)

abbrev Idx : Type := (Gen (level N r qv) S t) ⊕ (ZMod (level N r qv))ˣ

def dag : Idx N r qv S → CohCarrier.Gen (level N r qv) S
  | Sum.inl (Gen.T ℓ hℓ hℓS hℓL) => CohCarrier.Gen.T ℓ hℓ hℓS hℓL
  | Sum.inl (Gen.U i) => CohCarrier.Gen.U (qv i) (hq i) (dvd_level_q N r qv i)
  | Sum.inr d => CohCarrier.Gen.dia d

def opI : Idx N r qv S → Module.End 𝒪 (Carrier N r qv 𝒪 H)
  | Sum.inl g => op N r qv S 𝒪 H g
  | Sum.inr d => CohCarrier.diamondL (level N r qv) H 𝒪 d

theorem opI_eq_opFamily (i : Idx N r qv S) :
    opI N r qv S 𝒪 H i = CohCarrier.opFamily (level N r qv) H S 𝒪 (dag N r qv S hq i) := by
  rcases i with (⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | d <;> rfl

variable (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] 𝒪]

def gWI : Idx N r qv S →
    Module.End 𝒪 (𝒪 ⊗[ℤ_[p]] ↥(TateModule p (ModularCurve.JH (level N r qv) H)))
  | Sum.inl (Gen.T ℓ hℓ hℓS hℓL) =>
      (ModularCurve.tateGenOpH (level N r qv) H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓL)).baseChange 𝒪
  | Sum.inl (Gen.U i) =>
      (ModularCurve.tateGenOpH (level N r qv) H S p
        (CohCarrier.Gen.U (qv i) (hq i) (dvd_level_q N r qv i))).baseChange 𝒪
  | Sum.inr d => (ModularCurve.tateGenOpH (level N r qv) H S p (CohCarrier.Gen.dia d)).baseChange 𝒪

theorem gWI_eq (i : Idx N r qv S) :
    gWI N r qv S 𝒪 H hq p i =
      (ModularCurve.tateGenOpH (level N r qv) H S p (dag N r qv S hq i)).baseChange 𝒪 := by
  rcases i with (⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | d <;> rfl

variable [IsLocalRing 𝒪] (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
  (α : Fin t → IsLocalRing.ResidueField 𝒪) (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)

def gMI : Idx N r qv S → Module.End 𝒪 (ML N r qv S 𝒪 H θ α hc)
  | Sum.inl g => opML N r qv S 𝒪 H θ α hc (MvPolynomial.X g)
  | Sum.inr d => diaML N r qv S 𝒪 H θ α hc hdc d

end Families
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

section MainProof

open IsLocalRing CuspForm.TWLevel
open scoped IsMulCommutative

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem mainThm
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    [Algebra ℤ_[p] 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hq : ∀ i, (qv i).Prime)
    (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      ℓ ≡ 1 [MOD level N r qv] ∧
      θ (CuspForm.heckeAlgebra.T hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS) ≠
        (ℓ : ResidueField 𝒪) + 1) :
    ∃ (E : 𝒪 ⊗[ℤ_[p]] ↥(TateModule p (ModularCurve.JH (level N r qv) H)) →ₗ[𝒪]
        𝒪 ⊗[ℤ_[p]] ↥(TateModule p (ModularCurve.JH (level N r qv) H))),
      E ∘ₗ E = E ∧
      (∀ i : Idx N r qv S, E ∘ₗ gWI N r qv S 𝒪 H hq p i = gWI N r qv S 𝒪 H hq p i ∘ₗ E) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        E ∘ₗ (ModularCurve.JH.tateGaloisRep (level N r qv) H p σ).baseChange 𝒪 =
          (ModularCurve.JH.tateGaloisRep (level N r qv) H p σ).baseChange 𝒪 ∘ₗ E) ∧
      ∃ Θ : Module.Dual 𝒪 (ML N r qv S 𝒪 H θ α hc) →ₗ[𝒪]
          𝒪 ⊗[ℤ_[p]] ↥(TateModule p (ModularCurve.JH (level N r qv) H)),
        Function.Injective Θ ∧
        LinearMap.range Θ = LinearMap.range E ∧
        ∀ (i : Idx N r qv S) (y : Module.Dual 𝒪 (ML N r qv S 𝒪 H θ α hc)),
          Θ (y ∘ₗ gMI N r qv S 𝒪 H θ α hc hdc i) = gWI N r qv S 𝒪 H hq p i (Θ y) := by

  haveI : Module.Finite ℤ_[p] 𝒪 :=
    RibetIrr.module_finite_padicInt_of_isDiscreteValuationRing p 𝒪 hp𝒪
  haveI : Module.IsTorsionFree ℤ_[p] 𝒪 := isTorsionFree_padicInt 𝒪 p
  haveI : Module.Free ℤ_[p] 𝒪 := Module.free_of_finite_type_torsion_free'
  obtain ⟨hTfin, hTfree⟩ := ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH (level N r qv) p H
  haveI := hTfin
  haveI := hTfree
  haveI : Module.Finite 𝒪 (Carrier N r qv 𝒪 H) := CohCarrier.H1_moduleFinite (level N r qv) H 𝒪 𝒪
  have hres : Function.Surjective (algebraMap 𝒪 (ResidueField 𝒪)) := by
    rw [ResidueField.algebraMap_eq]; exact residue_surjective
  let D : CohCarrier.HeckeData 𝒪 (Carrier N r qv 𝒪 H) (ResidueField 𝒪) :=
    heckeData N r qv S 𝒪 H θ α hc
  obtain ⟨Sp⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra D

  have hin := ModularCurve.heckeDiamondInputsHAll (level N r qv) H
  refine (ModularCurve.exists_heckeEquivariant_parabolicHoms_to_dual_baseChange_tateModule_jH
    (level N r qv) p H S hin 𝒪).elim fun Φ hΦ => ?_
  rcases hΦ with ⟨hΦeq, hΦsurj, hΦinj⟩

  let Vp : Submodule 𝒪 (Carrier N r qv 𝒪 H) :=
    ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH (level N r qv) H) 𝒪
  have hstab : ∀ i : Idx N r qv S, ∀ v ∈ Vp, opI N r qv S 𝒪 H i v ∈ Vp := by
    rintro ((⟨ℓ, hℓ, hℓS, hℓL⟩ | i) | d) v hv
    · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact CohCarrier.heckeT_mem_parabolicHoms (level N r qv) H 𝒪 ℓ v hv
    · exact CohCarrier.heckeT_mem_parabolicHoms (level N r qv) H 𝒪 (qv i) v hv
    · exact diamondL_mem_parabolicHoms (level N r qv) H 𝒪 d v hv
  have hadj : ∀ i : Idx N r qv S, ∀ v ∈ Vp,
      Φ (opI N r qv S 𝒪 H i v) = Φ v ∘ₗ gWI N r qv S 𝒪 H hq p i := by
    intro i v hv
    rw [opI_eq_opFamily N r qv S 𝒪 H hq, gWI_eq]
    exact hΦeq _ v hv

  have hdat : ∃ (a : Module.End 𝒪 (Carrier N r qv 𝒪 H)) (c₀ : D.FreeAlg),
      a * a = a ∧ (∀ v, a v ∈ Vp) ∧ D.opAlgHom c₀ = a ∧
      (∀ i : Idx N r qv S, opI N r qv S 𝒪 H i * a = a * opI N r qv S 𝒪 H i) ∧
      ∃ ι : corner a ≃ₗ[𝒪] ML N r qv S 𝒪 H θ α hc,
        ∀ (i : Idx N r qv S) (u u' : corner a), (u' : Carrier N r qv 𝒪 H) = opI N r qv S 𝒪 H i u →
          ι u' = gMI N r qv S 𝒪 H θ α hc hdc i (ι u) := by
    by_cases hker : RingHom.ker (phiA D) ≤ D.mTheta
    ·
      obtain ⟨i₀, hi₀⟩ := exists_index D hres Sp hker
      obtain ⟨c₀, hc₀, hc₀e⟩ := exists_lift D Sp i₀ hi₀

      obtain ⟨ℓ₀, hℓ₀, hℓ₀S, hℓ₀L, hℓ₀1, hne⟩ := hEis
      haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩
      let g₀ : D.Gen := Gen.T ℓ₀ hℓ₀ hℓ₀S hℓ₀L
      set T₀ : D.FreeAlg := MvPolynomial.X g₀ - MvPolynomial.C ((ℓ₀ : 𝒪) + 1) with hT₀def
      have hT₀ : T₀ ∉ D.mTheta := by
        intro h
        apply hne
        have h' : D.thetaTilde T₀ = 0 := h
        rw [hT₀def, thetaTilde_X_sub_C, sub_eq_zero, map_add, map_natCast, map_one] at h'
        exact h'
      have haVp : ∀ v, eEnd D Sp i₀ v ∈ Vp := by
        intro v
        obtain ⟨w₀, e2⟩ := exists_opAlgHom_apply_eq D Sp i₀ hi₀ T₀ hT₀ v
        rw [← e2]
        set w := eEnd D Sp i₀ w₀ with hw
        have e3 : D.opAlgHom T₀ w =
            CohCarrier.heckeT (level N r qv) H ℓ₀ 𝒪 w - (ℓ₀ + 1) • w := by
          rw [hT₀def, opAlgHom_X_sub_C_apply, ← Nat.cast_succ, Nat.cast_smul_eq_nsmul]
          rfl
        rw [e3]
        exact CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one (level N r qv) H 𝒪 w
          ℓ₀ hℓ₀ hℓ₀L hℓ₀1
      refine ⟨eEnd D Sp i₀, c₀, eEnd_mul_eEnd D Sp i₀, haVp, hc₀e, ?_, iotaEquiv D Sp i₀ hi₀, ?_⟩
      · rintro (g | d)
        · exact op_mul_eEnd D Sp i₀ g
        · show CohCarrier.diamondL (level N r qv) H 𝒪 d * eEnd D Sp i₀ =
            eEnd D Sp i₀ * CohCarrier.diamondL (level N r qv) H 𝒪 d
          rw [← hc₀e]
          exact diamondL_opAlgHom_comm N r qv S 𝒪 H θ α hc hdc d c₀
      · rintro (g | d) u u' hu'
        · rw [iotaEquiv_apply, iotaEquiv_apply, hu']
          show D.toML (D.op g u) = (MvPolynomial.X g : D.FreeAlg) • D.toML u
          rw [← CohCarrier.HeckeData.opAlgHom_X, toML_opAlgHom]
        · rw [iotaEquiv_apply, iotaEquiv_apply, hu']
          exact (diaML_toML N r qv S 𝒪 H θ α hc hdc d _).symm
    ·
      obtain ⟨s, hs1, hs2⟩ := SetLike.not_le_iff_exists.mp hker
      have hs0 : D.opAlgHom s = 0 := by
        rw [← coe_phiA, show phiA D s = 0 from hs1]; rfl
      have hML : ∀ x : ML N r qv S 𝒪 H θ α hc, x = 0 := ML_eq_zero_of D s hs2 hs0
      haveI : Subsingleton (ML N r qv S 𝒪 H θ α hc) := ⟨fun x y => by rw [hML x, hML y]⟩
      haveI : Subsingleton ↥(corner (0 : Module.End 𝒪 (Carrier N r qv 𝒪 H))) := ⟨fun x y => by
        apply Subtype.ext
        obtain ⟨_, hx⟩ := LinearMap.mem_range.mp x.2
        obtain ⟨_, hy⟩ := LinearMap.mem_range.mp y.2
        rw [← hx, ← hy]; rfl⟩
      refine ⟨0, 0, mul_zero 0, fun v => Vp.zero_mem, map_zero _, fun i => by rw [mul_zero, zero_mul],
        LinearEquiv.ofSubsingleton _ _, fun i u u' _ => Subsingleton.elim _ _⟩
  obtain ⟨a, c₀, ha2, haVp, hc₀a, hcomm, ι, hι⟩ := hdat

  have hσ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      tr Vp Φ hΦsurj hΦinj a * (ModularCurve.JH.tateGaloisRep (level N r qv) H p σ).baseChange 𝒪 =
        (ModularCurve.JH.tateGaloisRep (level N r qv) H p σ).baseChange 𝒪 * tr Vp Φ hΦsurj hΦinj a := by
    intro σ
    rw [← hc₀a]
    refine tr_aeval_comm Vp Φ hΦsurj hΦinj (op N r qv S 𝒪 H) (fun g => hstab (Sum.inl g))
      D.opAlgHom D.opAlgHom_X _ (fun g => ?_) c₀
    rw [← eq_tr_of_adjoint Vp Φ hΦsurj hΦinj (op N r qv S 𝒪 H g) (gWI N r qv S 𝒪 H hq p (Sum.inl g))
      (hadj (Sum.inl g)), gWI_eq]
    exact baseChange_comp_comm (tateGaloisRep_comp_tateGenOpH (level N r qv) H S p σ _).symm

  exact package Vp Φ hΦsurj hΦinj a ha2 haVp ι (opI N r qv S 𝒪 H) (gWI N r qv S 𝒪 H hq p)
    (gMI N r qv S 𝒪 H θ α hc hdc) hadj hstab hcomm
    (fun i u => hι i u (restrictCorner a (opI N r qv S 𝒪 H i) (hcomm i) u) rfl)
    (fun σ => (ModularCurve.JH.tateGaloisRep (level N r qv) H p σ).baseChange 𝒪) hσ

end MainProof
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

end A2Comp
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

end
p2m_reactivate "P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH.A2Comp"

open IsLocalRing CuspForm.TWLevel TensorProduct in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    [Algebra ℤ_[p] 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hq : ∀ i, (qv i).Prime)
    (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)

    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      ℓ ≡ 1 [MOD level N r qv] ∧
      θ (CuspForm.heckeAlgebra.T hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS) ≠
        (ℓ : ResidueField 𝒪) + 1) :
    ∃ (E : 𝒪 ⊗[ℤ_[p]] ↥(TateModule p (ModularCurve.JH (level N r qv) H)) →ₗ[𝒪]
        𝒪 ⊗[ℤ_[p]] ↥(TateModule p (ModularCurve.JH (level N r qv) H))),

      E ∘ₗ E = E ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
        E ∘ₗ (ModularCurve.tateGenOpH (level N r qv) H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓL)).baseChange 𝒪 =
          (ModularCurve.tateGenOpH (level N r qv) H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓL)).baseChange 𝒪 ∘ₗ E) ∧
      (∀ i : Fin t,
        E ∘ₗ (ModularCurve.tateGenOpH (level N r qv) H S p
            (CohCarrier.Gen.U (qv i) (hq i) (dvd_level_q N r qv i))).baseChange 𝒪 =
          (ModularCurve.tateGenOpH (level N r qv) H S p
            (CohCarrier.Gen.U (qv i) (hq i) (dvd_level_q N r qv i))).baseChange 𝒪 ∘ₗ E) ∧
      (∀ d : (ZMod (level N r qv))ˣ,
        E ∘ₗ (ModularCurve.tateGenOpH (level N r qv) H S p (CohCarrier.Gen.dia d)).baseChange 𝒪 =
          (ModularCurve.tateGenOpH (level N r qv) H S p (CohCarrier.Gen.dia d)).baseChange 𝒪 ∘ₗ E) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        E ∘ₗ (ModularCurve.JH.tateGaloisRep (level N r qv) H p σ).baseChange 𝒪 =
          (ModularCurve.JH.tateGaloisRep (level N r qv) H p σ).baseChange 𝒪 ∘ₗ E) ∧

      ∃ Θ : Module.Dual 𝒪 (ML N r qv S 𝒪 H θ α hc) →ₗ[𝒪]
          𝒪 ⊗[ℤ_[p]] ↥(TateModule p (ModularCurve.JH (level N r qv) H)),
        Function.Injective Θ ∧
        LinearMap.range Θ = LinearMap.range E ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv)
            (y : Module.Dual 𝒪 (ML N r qv S 𝒪 H θ α hc)),
          Θ (y ∘ₗ opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL))) =
            (ModularCurve.tateGenOpH (level N r qv) H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓL)).baseChange 𝒪
              (Θ y)) ∧
        (∀ (i : Fin t) (y : Module.Dual 𝒪 (ML N r qv S 𝒪 H θ α hc)),
          Θ (y ∘ₗ opML N r qv S 𝒪 H θ α hc (MvPolynomial.X (Gen.U i))) =
            (ModularCurve.tateGenOpH (level N r qv) H S p
              (CohCarrier.Gen.U (qv i) (hq i) (dvd_level_q N r qv i))).baseChange 𝒪 (Θ y)) ∧
        (∀ (u : (ZMod (level N r qv))ˣ) (y : Module.Dual 𝒪 (ML N r qv S 𝒪 H θ α hc)),
          Θ (y ∘ₗ diaML N r qv S 𝒪 H θ α hc hdc u) =
            (ModularCurve.tateGenOpH (level N r qv) H S p (CohCarrier.Gen.dia u)).baseChange 𝒪 (Θ y)) := by
  refine (A2Comp.mainThm p hp𝒪 S N r θ qv hq α H hc hdc hEis).elim fun E hE => ?_
  rcases hE with ⟨hEE, hEcomm, hEσ, Θ, hΘinj, hΘrange, hΘeq⟩
  exact ⟨E, hEE, fun ℓ hℓ hℓS hℓL => hEcomm (Sum.inl (Gen.T ℓ hℓ hℓS hℓL)),
    fun i => hEcomm (Sum.inl (Gen.U i)), fun d => hEcomm (Sum.inr d), hEσ, Θ, hΘinj, hΘrange,
    fun ℓ hℓ hℓS hℓL y => hΘeq (Sum.inl (Gen.T ℓ hℓ hℓS hℓL)) y,
    fun i y => hΘeq (Sum.inl (Gen.U i)) y, fun u y => hΘeq (Sum.inr u) y⟩

end S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH
end P2MW
export P2MW.S_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH (solution)

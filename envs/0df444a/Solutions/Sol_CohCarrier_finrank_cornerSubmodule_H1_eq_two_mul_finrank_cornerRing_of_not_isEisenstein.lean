-- Prove2me | solution 1 for CohCarrier.finrank_cornerSubmodule_H1_eq_two_mul_finrank_cornerRing_of_not_isEisenstein
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/729b203e-97e3-5a19-80ec-82e653e4c078

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
import Theorems.Thm_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two
import Theorems.Thm_Matrix_finrank_range_and_eigenspace_of_adjoin_intCast
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_finrank_cornerRing_of_not_isEisenstein
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex CuspForm.GammaH_finiteIndex CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0"
p2m_attr_erase "instance" "FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero CohCarrier.jConjGammaH_jConjGammaH"
p2m_attr_erase "simp" "CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne"
p2m_attr_erase "simp" "CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open Module IharaLemma

namespace RANKGH

section CornerRing

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable (Sp : IdempotentSplitting B) (i : Fin Sp.n)

theorem toCornerRing_e : Sp.toCornerRing i (Sp.e i) = 1 := by
  apply Subtype.ext
  show Sp.e i * Sp.e i * Sp.e i = Sp.e i
  rw [(Sp.idem i).eq, (Sp.idem i).eq]

theorem toCornerRing_algebraMap (r : 𝒪) :
    Sp.toCornerRing i (algebraMap 𝒪 B r) = algebraMap 𝒪 (Sp.CornerRing i) r := rfl

theorem 𝔪_eq_ker {k : Type} [Field k] [Algebra 𝒪 k] (hsurj : Function.Surjective (algebraMap 𝒪 k))
    (πk : Sp.CornerRing i →ₐ[𝒪] k) :
    Sp.𝔪 i = RingHom.ker (πk.toRingHom.comp (Sp.toCornerRing i)) := by
  set f : B →+* k := πk.toRingHom.comp (Sp.toCornerRing i) with hf
  have hfsurj : Function.Surjective f := by
    intro x
    obtain ⟨r, rfl⟩ := hsurj x
    refine ⟨algebraMap 𝒪 B r, ?_⟩
    show πk (Sp.toCornerRing i (algebraMap 𝒪 B r)) = _
    rw [toCornerRing_algebraMap, AlgHom.commutes]
  have hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hfsurj
  obtain ⟨j, hj⟩ := Sp.exists_eq _ hmax
  have hnot : Sp.e i ∉ RingHom.ker f := by
    intro h
    rw [RingHom.mem_ker] at h
    change πk (Sp.toCornerRing i (Sp.e i)) = 0 at h
    rw [toCornerRing_e, map_one] at h
    exact one_ne_zero h
  by_cases hji : j = i
  · subst hji; exact hj
  · exact absurd (hj ▸ Sp.mem_of_ne (Ne.symm hji)) hnot

theorem exists_mul_mul_e_eq {u : B} (hu : u ∉ Sp.𝔪 i) : ∃ t : B, t * u * Sp.e i = Sp.e i :=
  exists_mul_mul_eq_of_notMem (Sp.idem i) (Sp.𝔪 i) (Sp.mem_of_isMaximal_of_ne i) hu

end CornerRing

section Module

variable (𝒪 : Type) [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
variable (Sp : IdempotentSplitting B) (i : Fin Sp.n)
variable (W : Submodule 𝒪 V) (hW : ∀ (b : B) (v : V), v ∈ W → b • v ∈ W)

def act (b : B) : V →ₗ[𝒪] V where
  toFun v := b • v
  map_add' v w := smul_add b v w
  map_smul' r v := smul_comm b r v

@[scoped simp] theorem act_apply (b : B) (v : V) : act 𝒪 b v = b • v := rfl

def resAlg : B →ₐ[𝒪] Module.End 𝒪 W where
  toFun b := (act 𝒪 b).restrict fun v hv => hW b v hv
  map_one' := by ext w; simp
  map_mul' a b := by ext w; simp [mul_smul]
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp [add_smul]
  commutes' r := by
    ext w
    simp [Algebra.algebraMap_eq_smul_one]

@[scoped simp] theorem coe_resAlg_apply (b : B) (w : W) : ((resAlg 𝒪 W hW b w : W) : V) = b • (w : V) := rfl

include hW in

theorem e_smul_mem {u : B} (hu : u ∉ Sp.𝔪 i) (huW : ∀ v : V, u • v ∈ W) (v : V) :
    Sp.e i • v ∈ W := by
  obtain ⟨t, ht⟩ := exists_mul_mul_e_eq Sp i hu
  rw [← ht, mul_smul, mul_smul]
  exact hW t _ (huW _)

theorem finrank_cornerSubmodule_eq (he : ∀ v : V, Sp.e i • v ∈ W) :
    Module.finrank 𝒪 ↥(cornerSubmodule (M := V) (Sp.e i)) =
      Module.finrank 𝒪 ↥(LinearMap.range (resAlg 𝒪 W hW (Sp.e i))) := by
  let f : ↥(cornerSubmodule (M := V) (Sp.e i)) →ₗ[𝒪] ↥(LinearMap.range (resAlg 𝒪 W hW (Sp.e i))) :=
    { toFun := fun x => ⟨⟨(x : V), by
          obtain ⟨y, hy⟩ := x.2
          rw [← hy]
          exact he y⟩, by
          obtain ⟨y, hy⟩ := x.2
          refine ⟨⟨Sp.e i • y, he y⟩, Subtype.ext ?_⟩
          simp only [coe_resAlg_apply]
          rw [← hy]
          show Sp.e i • Sp.e i • y = (Sp.e i • LinearMap.id (R := B)) y
          rw [smul_smul, (Sp.idem i).eq]
          rfl⟩
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : ↥(LinearMap.range (resAlg 𝒪 W hW (Sp.e i))) => ((z : W) : V)) hxy
  · rintro ⟨w, ⟨w0, rfl⟩⟩
    refine ⟨⟨Sp.e i • (w0 : V), ⟨(w0 : V), rfl⟩⟩, Subtype.ext (Subtype.ext rfl)⟩

variable (hfaith : ∀ b : B, (∀ v : V, b • v = 0) → b = 0)

include hfaith in

theorem e_mul_eq_zero_of_resAlg_eq_zero (he : ∀ v : V, Sp.e i • v ∈ W) {b : B}
    (hb : resAlg 𝒪 W hW b = 0) : Sp.e i * b = 0 := by
  apply hfaith
  intro v
  rw [mul_comm, mul_smul]
  have := congrArg (fun f : Module.End 𝒪 W => ((f ⟨Sp.e i • v, he v⟩ : W) : V)) hb
  simpa using this

include hfaith in

theorem finrank_cornerRing_eq (he : ∀ v : V, Sp.e i • v ∈ W) :
    Module.finrank 𝒪 (Sp.CornerRing i) =
      Module.finrank 𝒪 ↥(LinearMap.range (LinearMap.mulLeft 𝒪 (resAlg 𝒪 W hW (Sp.e i)) ∘ₗ
        (resAlg 𝒪 W hW).range.val.toLinearMap)) := by
  let val𝒪 : Sp.CornerRing i →ₗ[𝒪] B :=
    ((cornerSubmodule (M := B) (Sp.e i)).restrictScalars 𝒪).subtype ∘ₗ
      (Sp.cornerRingLinearEquiv i 𝒪).toLinearMap
  have hval𝒪 : ∀ z : Sp.CornerRing i, val𝒪 z = (z : B) := fun z => rfl
  let g : Sp.CornerRing i →ₗ[𝒪] Module.End 𝒪 W := (resAlg 𝒪 W hW).toLinearMap ∘ₗ val𝒪
  have hg : ∀ z : Sp.CornerRing i, g z = resAlg 𝒪 W hW (z : B) := fun z => rfl
  have hg_inj : Function.Injective g := by
    intro x y hxy
    rw [hg, hg] at hxy
    have h0 : resAlg 𝒪 W hW ((x : B) - (y : B)) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hxy
    have h1 := e_mul_eq_zero_of_resAlg_eq_zero 𝒪 Sp i W hW hfaith he h0
    rw [mul_sub, Sp.e_mul_coe, Sp.e_mul_coe, sub_eq_zero] at h1
    exact Subtype.ext h1
  have hg_range : LinearMap.range g =
      LinearMap.range (LinearMap.mulLeft 𝒪 (resAlg 𝒪 W hW (Sp.e i)) ∘ₗ
        (resAlg 𝒪 W hW).range.val.toLinearMap) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨⟨resAlg 𝒪 W hW (z : B), ⟨(z : B), rfl⟩⟩, ?_⟩
      rw [hg]
      show resAlg 𝒪 W hW (Sp.e i) * resAlg 𝒪 W hW (z : B) = resAlg 𝒪 W hW (z : B)
      rw [← map_mul, Sp.e_mul_coe]
    · rintro _ ⟨⟨_, ⟨b, rfl⟩⟩, rfl⟩
      refine ⟨Sp.toCornerRing i b, ?_⟩
      rw [hg]
      show resAlg 𝒪 W hW (Sp.e i * b * Sp.e i) = resAlg 𝒪 W hW (Sp.e i) * resAlg 𝒪 W hW b
      rw [mul_comm (Sp.e i) b, mul_assoc, (Sp.idem i).eq, mul_comm b, map_mul]
  rw [← hg_range]
  exact (LinearEquiv.ofInjective g hg_inj).finrank_eq

end Module

section Transport

variable {R : Type*} [CommRing R] {Wm : Type*} [AddCommGroup Wm] [Module R Wm] {n : ℕ}
variable (bR : Basis (Fin n) R Wm)

abbrev Φm : Module.End R Wm ≃ₐ[R] Matrix (Fin n) (Fin n) R := LinearMap.toMatrixAlgEquiv bR

theorem Φm_apply (x : Module.End R Wm) : Φm bR x = LinearMap.toMatrix bR bR x := rfl

abbrev ΦmH : Module.End R Wm →ₐ[R] Matrix (Fin n) (Fin n) R :=
  (Φm bR : Module.End R Wm →ₐ[R] Matrix (Fin n) (Fin n) R)

@[scoped simp] theorem ΦmH_apply (x : Module.End R Wm) : ΦmH bR x = Φm bR x := rfl

theorem toLin'_Φm_apply (x : Module.End R Wm) (w : Wm) :
    Matrix.toLin' (Φm bR x) (bR.equivFun w) = bR.equivFun (x w) := by
  rw [Matrix.toLin'_apply, Φm_apply, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr]

theorem toLin'_Φm_comp (x : Module.End R Wm) :
    Matrix.toLin' (Φm bR x) ∘ₗ (bR.equivFun : Wm →ₗ[R] (Fin n → R)) =
      (bR.equivFun : Wm →ₗ[R] (Fin n → R)) ∘ₗ x := by
  ext w
  exact congrFun (toLin'_Φm_apply bR x w) _

theorem finrank_range_toLin'_Φm (x : Module.End R Wm) :
    Module.finrank R ↥(LinearMap.range (Matrix.toLin' (Φm bR x))) =
      Module.finrank R ↥(LinearMap.range x) := by
  have h : LinearMap.range (Matrix.toLin' (Φm bR x)) =
      (LinearMap.range x).map (bR.equivFun : Wm →ₗ[R] (Fin n → R)) := by
    rw [LinearMap.range_eq_map x, ← Submodule.map_comp, ← toLin'_Φm_comp, Submodule.map_comp,
      Submodule.map_top, LinearEquiv.range, Submodule.map_top]
  rw [h]
  exact LinearEquiv.finrank_map_eq _ _

variable (A : Subalgebra R (Module.End R Wm))

theorem finrank_range_mulLeft_Φm (x : Module.End R Wm) :
    Module.finrank R ↥(LinearMap.range (LinearMap.mulLeft R (Φm bR x) ∘ₗ
        (A.map (ΦmH bR)).val.toLinearMap)) =
      Module.finrank R ↥(LinearMap.range (LinearMap.mulLeft R x ∘ₗ A.val.toLinearMap)) := by
  have h : LinearMap.range (LinearMap.mulLeft R (Φm bR x) ∘ₗ
        (A.map (ΦmH bR)).val.toLinearMap) =
      (LinearMap.range (LinearMap.mulLeft R x ∘ₗ A.val.toLinearMap)).map
        ((Φm bR).toLinearEquiv : Module.End R Wm →ₗ[R] Matrix (Fin n) (Fin n) R) := by
    apply le_antisymm
    · rintro _ ⟨⟨a', ha'⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.mp ha'
      refine ⟨x * a, ⟨⟨a, ha⟩, rfl⟩, ?_⟩
      show Φm bR (x * a) = Φm bR x * Φm bR a
      rw [map_mul]
    · rintro _ ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
      refine ⟨⟨Φm bR a, Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
      show Φm bR x * Φm bR a = Φm bR (x * a)
      rw [map_mul]
  rw [h]
  exact LinearEquiv.finrank_map_eq _ _

abbrev idxEquiv : ↥A ≃ₐ[R] ↥(A.map (ΦmH bR)) :=
  (Φm bR).subalgebraMap A

theorem coe_idxEquiv (a : A) :
    ((idxEquiv bR A a : ↥(A.map (ΦmH bR))) :
      Matrix (Fin n) (Fin n) R) = Φm bR a :=
  AlgEquiv.subalgebraMap_apply_coe _ _ _

theorem finrank_iInf_eigenspace_Φm
    (g : ↥(A.map (ΦmH bR)) → R) :
    Module.finrank R ↥(⨅ a' : ↥(A.map (ΦmH bR)),
        Module.End.eigenspace (Matrix.toLin' (a' : Matrix (Fin n) (Fin n) R)) (g a')) =
      Module.finrank R ↥(⨅ a : A, Module.End.eigenspace (a : Module.End R Wm)
        (g (idxEquiv bR A a))) := by
  set E' := ⨅ a' : ↥(A.map (ΦmH bR)),
        Module.End.eigenspace (Matrix.toLin' (a' : Matrix (Fin n) (Fin n) R)) (g a') with hE'
  have hcomap : E'.comap (bR.equivFun : Wm →ₗ[R] (Fin n → R)) =
      ⨅ a : A, Module.End.eigenspace (a : Module.End R Wm) (g (idxEquiv bR A a)) := by
    rw [hE', Submodule.comap_iInf]
    rw [← Equiv.iInf_comp (idxEquiv bR A).toEquiv]
    refine iInf_congr fun a => ?_
    ext w
    simp only [Submodule.mem_comap, Module.End.mem_eigenspace_iff, AlgEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, coe_idxEquiv]
    change Matrix.toLin' (Φm bR a) (bR.equivFun w) = _ ↔ _
    rw [toLin'_Φm_apply, ← map_smul]
    exact bR.equivFun.injective.eq_iff
  rw [← hcomap, Submodule.comap_equiv_eq_map_symm]
  exact (LinearEquiv.finrank_map_eq _ _).symm

theorem exists_bijective_of_basis {d : ℕ} (β : Module.Basis (Fin d) A Wm) :
    ∃ v : Fin d → (Fin n → R), Function.Bijective
      (fun c : Fin d → ↥(A.map (ΦmH bR)) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) R).mulVec (v k))) := by
  refine ⟨fun k => bR.equivFun (β k), ?_⟩
  let e0 : (Fin d → ↥(A.map (ΦmH bR))) ≃ (Fin d → A) :=
    Equiv.arrowCongr (Equiv.refl _) (idxEquiv bR A).symm.toEquiv
  have hfac : (fun c : Fin d → ↥(A.map (ΦmH bR)) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) R).mulVec (bR.equivFun (β k)))) =
      (bR.equivFun : Wm → (Fin n → R)) ∘ (β.equivFun.symm : (Fin d → A) → Wm) ∘ e0 := by
    funext c
    simp only [Function.comp_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : ((c k : Matrix (Fin n) (Fin n) R)) = Φm bR ((idxEquiv bR A).symm (c k) : A) := by
      have := coe_idxEquiv bR A ((idxEquiv bR A).symm (c k))
      rw [AlgEquiv.apply_symm_apply] at this
      exact this
    rw [hk, ← Matrix.toLin'_apply, toLin'_Φm_apply]
    rfl
  rw [hfac]
  exact bR.equivFun.bijective.comp (β.equivFun.symm.bijective.comp e0.bijective)

end Transport

section Stable

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup CohCarrier ModularCurve.Period
open scoped MatrixGroups

variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]

theorem heckeT_apply_eq_sum (φ : H1 M Hs A) (u : ↥(GammaH M Hs))
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)))] :
    heckeT M Hs ℓ A φ (Additive.ofMul u) =
      ∑ O : Quotient (MulAction.orbitRel (Subgroup.zpowers u)
          (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)),
        φ (Additive.ofMul (conjL M Hs ℓ
          ⟨O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out⟩)) := by
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M Hs ℓ)) u) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  rfl

theorem trace_conjUpperMat (X : SL(2, ℤ)) (hX : (ℓ : ℤ) ∣ X 0 1) :
    ((conjUpperMat ℓ X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((X : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjUpperMat]

theorem trace_sq_conj_pow (γ r : SL(2, ℤ)) (m : ℕ)
    (hγ : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    (((r⁻¹ * γ ^ m * r : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  obtain ⟨ε, δ, h, hε, rfl⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four γ hγ
  have hu : ∀ n : ℕ, ((r⁻¹ * (δ * ModularGroup.T ^ h * δ⁻¹) ^ n * r : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    intro n
    rw [conj_pow, ← zpow_natCast, ← _root_.zpow_mul,
      show r⁻¹ * (δ * ModularGroup.T ^ (h * (n : ℤ)) * δ⁻¹) * r =
        (r⁻¹ * δ) * (ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹) by group,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      show ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹ * (r⁻¹ * δ) = ModularGroup.T ^ (h * (n : ℤ)) by group,
      ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
    ring
  rcases hε with rfl | rfl
  · rw [one_mul, hu]; norm_num
  · rw [neg_one_mul, neg_pow]
    rcases neg_one_pow_eq_or SL(2, ℤ) m with h1 | h1
    · rw [h1, one_mul, hu]; norm_num
    · rw [h1, neg_one_mul, mul_neg, neg_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
        neg_sq, hu]
      norm_num

theorem heckeT_isParabolicHom (φ : H1 M Hs A)
    (hφ : IsParabolicHom (GammaH M Hs) φ) :
    IsParabolicHom (GammaH M Hs) (heckeT M Hs ℓ A φ) := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers γ)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ))) := Fintype.ofFinite _
  rw [heckeT_apply_eq_sum]
  refine Finset.sum_eq_zero fun O _ => hφ _ ?_
  set x : ↥(GammaHUpper M Hs ℓ) := ⟨O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem _ γ O.out⟩ with hxdef
  have hx : ((conjL M Hs ℓ x : ↥(GammaH M Hs)) : SL(2, ℤ)) =
      conjUpperMat ℓ ((x : ↥(GammaH M Hs)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M Hs ℓ x) := rfl
  rw [hx, trace_conjUpperMat, hxdef]
  show ((((O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out : ↥(GammaH M Hs)) :
    SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  exact trace_sq_conj_pow _ _ _ hγ

theorem diamondRaw_isParabolicHom (σ : Gamma0 M) (φ : H1 M Hs A)
    (hφ : IsParabolicHom (GammaH M Hs) φ) :
    IsParabolicHom (GammaH M Hs) (diamondRaw M Hs A σ φ) := by
  intro γ hγ
  show φ (Additive.ofMul (conjHom M Hs σ γ)) = 0
  refine hφ _ ?_
  show ((((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    show (σ : SL(2, ℤ))⁻¹ * ((σ : SL(2, ℤ)) * (γ : SL(2, ℤ))) = γ by group]
  exact hγ

theorem diamondL_isParabolicHom [NeZero M] (R : Type) [CommRing R] (d : (ZMod M)ˣ) (φ : H1 M Hs R)
    (hφ : IsParabolicHom (GammaH M Hs) φ) :
    IsParabolicHom (GammaH M Hs) (diamondL M Hs R d φ) :=
  diamondRaw_isParabolicHom M Hs _ φ hφ

theorem coresAdd_comp {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex]
    {B : Type*} [AddCommGroup B] (f : A →+ B) (ψ : Additive ↥K →+ A) :
    coresAdd K (f.comp ψ) = f.comp (coresAdd K ψ) := by
  ext g
  simp only [coresAdd, MonoidHom.toAdditiveLeft_apply_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, map_sum]

theorem heckeT_eq_coresAdd (φ : H1 M Hs A) :
    heckeT M Hs ℓ A φ = coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL M Hs ℓ))) := rfl

theorem heckeT_comp_coeff {B : Type*} [AddCommGroup B] (f : A →+ B) (φ : H1 M Hs A) :
    heckeT M Hs ℓ B (f.comp φ) = f.comp (heckeT M Hs ℓ A φ) := by
  rw [heckeT_eq_coresAdd, heckeT_eq_coresAdd, ← coresAdd_comp]
  rfl

theorem diamondL_comp_coeff [NeZero M] (R R' : Type) [CommRing R] [CommRing R'] (d : (ZMod M)ˣ)
    (f : R →+ R') (φ : H1 M Hs R) :
    diamondL M Hs R' d (f.comp φ) = f.comp (diamondL M Hs R d φ) := rfl

end Stable

section Parabolic

open CongruenceSubgroup CohCarrier ModularCurve.Period
open scoped MatrixGroups

variable (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ)

theorem isCongruenceSubgroup_GammaH : IsCongruenceSubgroup (GammaH M Hs) := by
  refine ⟨M, NeZero.ne _, fun A hA => ?_⟩
  rw [Gamma_mem] at hA
  obtain ⟨_, _, h10, h11⟩ := hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact h10
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have : gamma0Units M ⟨A, h0⟩ = 1 := by
    apply Units.ext
    simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [this]; exact one_mem Hs

scoped instance finiteIndex_GammaH : (GammaH M Hs).FiniteIndex := (isCongruenceSubgroup_GammaH M Hs).finiteIndex

abbrev parR (R : Type) [CommRing R] : Submodule R (H1 M Hs R) :=
  parabolicHoms R (GammaH M Hs) R

theorem heckeT_mem_parR (R : Type) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (φ : H1 M Hs R)
    (hφ : φ ∈ parR M Hs R) : heckeT M Hs ℓ R φ ∈ parR M Hs R :=
  heckeT_isParabolicHom M Hs ℓ φ hφ

theorem diamondL_mem_parR (R : Type) [CommRing R] (d : (ZMod M)ˣ) (φ : H1 M Hs R)
    (hφ : φ ∈ parR M Hs R) : diamondL M Hs R d φ ∈ parR M Hs R :=
  diamondL_isParabolicHom M Hs R d φ hφ

abbrev Idx (S : Set ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ (ℓ ∉ S ∨ ℓ ∣ M)} ⊕ (ZMod M)ˣ

def TparI (S : Set ℕ) (R : Type) [CommRing R] : Idx M S → Module.End R ↥(parR M Hs R)
  | Sum.inl i =>
      haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩
      (heckeTL M Hs R i.1).restrict fun φ hφ => heckeT_mem_parR M Hs R i.1 φ hφ
  | Sum.inr d => (diamondL M Hs R d).restrict fun φ hφ => diamondL_mem_parR M Hs R d φ hφ

theorem coe_TparI_inl (S : Set ℕ) (R : Type) [CommRing R] (i : {ℓ : ℕ // ℓ.Prime ∧ (ℓ ∉ S ∨ ℓ ∣ M)})
    (φ : ↥(parR M Hs R)) :
    ((TparI M Hs S R (Sum.inl i) φ : ↥(parR M Hs R)) : H1 M Hs R) =
      (haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩; heckeT M Hs i.1 R φ) := rfl

theorem coe_TparI_inr (S : Set ℕ) (R : Type) [CommRing R] (d : (ZMod M)ˣ) (φ : ↥(parR M Hs R)) :
    ((TparI M Hs S R (Sum.inr d) φ : ↥(parR M Hs R)) : H1 M Hs R) = diamondL M Hs R d φ := rfl

def castPar (R : Type) [CommRing R] : ↥(parR M Hs ℤ) →+ ↥(parR M Hs R) where
  toFun φ := ⟨(Int.castAddHom R).comp (φ : H1 M Hs ℤ), by
    intro γ hγ
    show (Int.castAddHom R) ((φ : H1 M Hs ℤ) (Additive.ofMul γ)) = 0
    rw [φ.2 γ hγ, map_zero]⟩
  map_zero' := by ext; simp
  map_add' φ ψ := by ext; simp

theorem coe_castPar (R : Type) [CommRing R] (φ : ↥(parR M Hs ℤ)) :
    ((castPar M Hs R φ : ↥(parR M Hs R)) : H1 M Hs R) =
      (Int.castAddHom R).comp (φ : H1 M Hs ℤ) := rfl

theorem castPar_TparI (S : Set ℕ) (R : Type) [CommRing R] (i : Idx M S) (φ : ↥(parR M Hs ℤ)) :
    castPar M Hs R (TparI M Hs S ℤ i φ) = TparI M Hs S R i (castPar M Hs R φ) := by
  rcases i with i | d
  · haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩
    apply Subtype.ext
    show (Int.castAddHom R).comp (heckeT M Hs i.1 ℤ φ) =
      heckeT M Hs i.1 R ((Int.castAddHom R).comp (φ : H1 M Hs ℤ))
    rw [heckeT_comp_coeff]
  · apply Subtype.ext
    show (Int.castAddHom R).comp (diamondL M Hs ℤ d φ) =
      diamondL M Hs R d ((Int.castAddHom R).comp (φ : H1 M Hs ℤ))
    rw [diamondL_comp_coeff]

variable {M Hs}
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR M Hs ℤ))

def Mint (S : Set ℕ) (i : Idx M S) : Matrix (Fin n) (Fin n) ℤ := LinearMap.toMatrix b b (TparI M Hs S ℤ i)

variable {R : Type} [CommRing R] (bR : Module.Basis (Fin n) R ↥(parR M Hs R))
  (hbR : ∀ i, (bR i : H1 M Hs R) = (Int.castAddHom R).comp (b i : H1 M Hs ℤ))

include hbR in
theorem castPar_b (j : Fin n) : castPar M Hs R (b j) = bR j := Subtype.ext (hbR j).symm

include hbR in

theorem toMatrix_TparI (S : Set ℕ) (i : Idx M S) :
    LinearMap.toMatrix bR bR (TparI M Hs S R i) = (Mint b S i).map (Int.cast : ℤ → R) := by
  ext k j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, Mint]
  have hexp : TparI M Hs S ℤ i (b j) = ∑ k, (LinearMap.toMatrix b b (TparI M Hs S ℤ i) k j) • b k := by
    conv_lhs => rw [← b.sum_repr (TparI M Hs S ℤ i (b j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.toMatrix_apply]
  have h1 : TparI M Hs S R i (bR j) =
      ∑ k, ((LinearMap.toMatrix b b (TparI M Hs S ℤ i) k j : ℤ) : R) • bR k := by
    rw [← castPar_b b bR hbR j, ← castPar_TparI, hexp, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, castPar_b b bR hbR k]
    exact (Int.cast_smul_eq_zsmul R _ _).symm
  rw [h1]
  have h2 : bR.repr (∑ k, ((LinearMap.toMatrix b b (TparI M Hs S ℤ i) k j : ℤ) : R) • bR k) =
      Finsupp.equivFunOnFinite.symm fun k => ((LinearMap.toMatrix b b (TparI M Hs S ℤ i) k j : ℤ) : R) := by
    rw [← Module.Basis.equivFun_symm_apply]
    apply bR.repr.symm.injective
    simp [Module.Basis.equivFun]
  rw [h2]
  rfl

include hbR in

theorem map_adjoin_TparI (S : Set ℕ) :
    (Algebra.adjoin R (Set.range (TparI M Hs S R))).map (ΦmH bR) =
      Algebra.adjoin R (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → R)) := by
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  have h : (ΦmH bR : Module.End R ↥(parR M Hs R) → Matrix (Fin n) (Fin n) R) ∘ TparI M Hs S R =
      fun i => (Mint b S i).map (Int.cast : ℤ → R) := by
    funext i
    show Φm bR (TparI M Hs S R i) = _
    rw [Φm_apply, toMatrix_TparI b bR hbR]
  rw [h]

end Parabolic

section OverC

open CongruenceSubgroup CohCarrier ModularCurve.Period

variable (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (S : Set ℕ)

theorem genSet_eq (R : Type) [CommRing R] :
    {T : Module.End R ↥(parabolicHoms R (GammaH M Hs) R) |
        (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          ((T v : ↥(parabolicHoms R (GammaH M Hs) R)) : H1 M Hs R) =
            heckeT M Hs ℓ R (v : H1 M Hs R)) ∨
        (∃ d : (ZMod M)ˣ, ∀ v,
          ((T v : ↥(parabolicHoms R (GammaH M Hs) R)) : H1 M Hs R) =
            diamondL M Hs R d (v : H1 M Hs R))} =
      Set.range (TparI M Hs S R) := by
  ext T
  constructor
  · rintro (⟨ℓ, hℓ, hℓS, h⟩ | ⟨d, h⟩)
    · refine ⟨Sum.inl ⟨ℓ, hℓ, hℓS⟩, ?_⟩
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact (h v).symm
    · refine ⟨Sum.inr d, ?_⟩
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact (h v).symm
  · rintro ⟨(⟨ℓ, hℓ, hℓS⟩ | d), rfl⟩
    · exact Or.inl ⟨ℓ, hℓ, hℓS, fun v => rfl⟩
    · exact Or.inr ⟨d, fun v => rfl⟩

variable (hSfin : S.Finite)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR M Hs ℤ))
  (bC : Module.Basis (Fin n) ℂ ↥(parR M Hs ℂ))
  (hbC : ∀ i, (bC i : H1 M Hs ℂ) = (Int.castAddHom ℂ).comp (b i : H1 M Hs ℤ))

include hSfin hbC in
set_option maxHeartbeats 8000000 in

theorem descent_hypotheses :
    (∃ v : Fin 2 → (Fin n → ℂ), Function.Bijective
      (fun c : Fin 2 → ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k)))) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = 2 := by
  obtain ⟨⟨β⟩, hmult⟩ :=
    CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two M Hs S hSfin
  rw [genSet_eq M Hs S ℂ] at β hmult
  have hmap := map_adjoin_TparI b bC hbC S
  rw [← hmap]
  refine ⟨exists_bijective_of_basis bC _ β, fun χ => ?_⟩
  rw [finrank_iInf_eigenspace_Φm bC (Algebra.adjoin ℂ (Set.range (TparI M Hs S ℂ))) χ]
  exact hmult (χ.comp (idxEquiv bC (Algebra.adjoin ℂ (Set.range (TparI M Hs S ℂ)))).toAlgHom)

include hSfin hbC in

theorem descent (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [CharZero 𝒪] :
    ∀ ε ∈ Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪)),
      IsIdempotentElem ε →
        Module.finrank 𝒪 ↥(LinearMap.range (Matrix.toLin' ε)) =
          2 * Module.finrank 𝒪 ↥(LinearMap.range (LinearMap.mulLeft 𝒪 ε ∘ₗ
            (Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪))).val.toLinearMap)) := by
  obtain ⟨hfree, hmult⟩ := descent_hypotheses M Hs S hSfin b bC hbC
  exact (Matrix.finrank_range_and_eigenspace_of_adjoin_intCast n 2 (Mint b S) hfree hmult 𝒪).1

end OverC

section Assembly

open CongruenceSubgroup ModularCurve.Period CohCarrier
open scoped MatrixGroups IsMulCommutative

@[reducible] def cornerCommRing {B : Type} [CommRing B] (Sp : IdempotentSplitting B) (i : Fin Sp.n) :
    CommRing (Sp.CornerRing i) := inferInstance

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

variable (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [CharZero 𝒪]
    (k : Type) [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (hcomm : ∀ g h : Gen M S,
      opFamily M Hs S 𝒪 g * opFamily M Hs S 𝒪 h = opFamily M Hs S 𝒪 h * opFamily M Hs S 𝒪 g)
    (θbar : Gen M S → k)

abbrev TT : Type := ↥(hdata M Hs S 𝒪 k hcomm θbar).opSubalgebra

scoped instance : IsScalarTower 𝒪 (TT M Hs S 𝒪 k hcomm θbar) (H1 M Hs 𝒪) := ⟨fun r t v => rfl⟩

theorem TT_smul_def (t : TT M Hs S 𝒪 k hcomm θbar) (v : H1 M Hs 𝒪) :
    t • v = (t : Module.End 𝒪 (H1 M Hs 𝒪)) v := rfl

theorem TT_faithful (t : TT M Hs S 𝒪 k hcomm θbar) (h : ∀ v : H1 M Hs 𝒪, t • v = 0) : t = 0 :=
  Subtype.ext (LinearMap.ext h)

abbrev gen (g : Gen M S) : TT M Hs S 𝒪 k hcomm θbar :=
  ⟨(hdata M Hs S 𝒪 k hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

theorem gen_apply_mem (g : Gen M S) (v : H1 M Hs 𝒪) (hv : v ∈ parR M Hs 𝒪) :
    (hdata M Hs S 𝒪 k hcomm θbar).op g v ∈ parR M Hs 𝒪 := by
  show opFamily M Hs S 𝒪 g v ∈ parR M Hs 𝒪
  cases g with
  | T ℓ hℓ hℓS hℓM =>
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact heckeT_mem_parR M Hs 𝒪 ℓ v hv
  | U q hq hqM =>
      haveI : NeZero q := ⟨hq.ne_zero⟩
      exact heckeT_mem_parR M Hs 𝒪 q v hv
  | dia d =>
      exact diamondL_mem_parR M Hs 𝒪 d v hv

theorem TT_smul_mem (t : TT M Hs S 𝒪 k hcomm θbar) (v : H1 M Hs 𝒪) (hv : v ∈ parR M Hs 𝒪) :
    t • v ∈ parR M Hs 𝒪 := by
  rw [TT_smul_def]
  have ht : (t : Module.End 𝒪 (H1 M Hs 𝒪)) ∈ Algebra.adjoin 𝒪
      (Set.range (hdata M Hs S 𝒪 k hcomm θbar).op) := t.2
  revert v
  refine Algebra.adjoin_induction (p := fun x _ => ∀ v : H1 M Hs 𝒪, v ∈ parR M Hs 𝒪 →
      x v ∈ parR M Hs 𝒪) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨g, rfl⟩ v hv
    exact gen_apply_mem M Hs S 𝒪 k hcomm θbar g v hv
  · intro r v hv
    rw [Module.algebraMap_end_apply]
    exact (parR M Hs 𝒪).smul_mem r hv
  · intro x y _ _ hx hy v hv
    rw [LinearMap.add_apply]
    exact (parR M Hs 𝒪).add_mem (hx v hv) (hy v hv)
  · intro x y _ _ hx hy v hv
    rw [Module.End.mul_apply]
    exact hx _ (hy v hv)

abbrev res :=
  resAlg 𝒪 (B := TT M Hs S 𝒪 k hcomm θbar) (parR M Hs 𝒪) (TT_smul_mem M Hs S 𝒪 k hcomm θbar)

theorem coe_res_apply (t : TT M Hs S 𝒪 k hcomm θbar) (w : ↥(parR M Hs 𝒪)) :
    ((res M Hs S 𝒪 k hcomm θbar t w : ↥(parR M Hs 𝒪)) : H1 M Hs 𝒪) =
      (t : Module.End 𝒪 (H1 M Hs 𝒪)) w := rfl

theorem range_res :
    (res M Hs S 𝒪 k hcomm θbar).range = Algebra.adjoin 𝒪 (Set.range (TparI M Hs S 𝒪)) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    have ht : (t : Module.End 𝒪 (H1 M Hs 𝒪)) ∈ Algebra.adjoin 𝒪
        (Set.range (hdata M Hs S 𝒪 k hcomm θbar).op) := t.2
    have key : ∀ (x : Module.End 𝒪 (H1 M Hs 𝒪)) (hx : x ∈ Algebra.adjoin 𝒪
        (Set.range (hdata M Hs S 𝒪 k hcomm θbar).op)),
        res M Hs S 𝒪 k hcomm θbar ⟨x, hx⟩ ∈ Algebra.adjoin 𝒪 (Set.range (TparI M Hs S 𝒪)) := by
      intro x hx
      refine Algebra.adjoin_induction (p := fun x hx => res M Hs S 𝒪 k hcomm θbar ⟨x, hx⟩ ∈
        Algebra.adjoin 𝒪 (Set.range (TparI M Hs S 𝒪))) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨g, rfl⟩
        cases g with
        | T ℓ hℓ hℓS hℓM =>
            refine Algebra.subset_adjoin ⟨Sum.inl ⟨ℓ, hℓ, Or.inl hℓS⟩, ?_⟩
            exact LinearMap.ext fun w => Subtype.ext rfl
        | U q hq hqM =>
            refine Algebra.subset_adjoin ⟨Sum.inl ⟨q, hq, Or.inr hqM⟩, ?_⟩
            exact LinearMap.ext fun w => Subtype.ext rfl
        | dia d =>
            refine Algebra.subset_adjoin ⟨Sum.inr d, ?_⟩
            exact LinearMap.ext fun w => Subtype.ext rfl
      · intro r
        have h1 : res M Hs S 𝒪 k hcomm θbar ⟨algebraMap 𝒪 _ r, Subalgebra.algebraMap_mem _ r⟩ =
            algebraMap 𝒪 _ r := (res M Hs S 𝒪 k hcomm θbar).commutes r
        rw [h1]
        exact Subalgebra.algebraMap_mem _ r
      · intro x y hx hy hpx hpy
        have h1 : res M Hs S 𝒪 k hcomm θbar ⟨x + y, Subalgebra.add_mem _ hx hy⟩ =
            res M Hs S 𝒪 k hcomm θbar ⟨x, hx⟩ + res M Hs S 𝒪 k hcomm θbar ⟨y, hy⟩ :=
          (map_add (res M Hs S 𝒪 k hcomm θbar) ⟨x, hx⟩ ⟨y, hy⟩)
        rw [h1]
        exact Subalgebra.add_mem _ hpx hpy
      · intro x y hx hy hpx hpy
        have h1 : res M Hs S 𝒪 k hcomm θbar ⟨x * y, Subalgebra.mul_mem _ hx hy⟩ =
            res M Hs S 𝒪 k hcomm θbar ⟨x, hx⟩ * res M Hs S 𝒪 k hcomm θbar ⟨y, hy⟩ :=
          (map_mul (res M Hs S 𝒪 k hcomm θbar) ⟨x, hx⟩ ⟨y, hy⟩)
        rw [h1]
        exact Subalgebra.mul_mem _ hpx hpy
    exact key t.1 ht
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨(⟨ℓ, hℓ, hℓS⟩ | d), rfl⟩
    · by_cases hℓM : ℓ ∣ M
      · refine ⟨gen M Hs S 𝒪 k hcomm θbar (Gen.U ℓ hℓ hℓM), ?_⟩
        exact LinearMap.ext fun w => Subtype.ext rfl
      · have hℓS' : ℓ ∉ S := hℓS.resolve_right hℓM
        refine ⟨gen M Hs S 𝒪 k hcomm θbar (Gen.T ℓ hℓ hℓS' hℓM), ?_⟩
        exact LinearMap.ext fun w => Subtype.ext rfl
    · refine ⟨gen M Hs S 𝒪 k hcomm θbar (Gen.dia d), ?_⟩
      exact LinearMap.ext fun w => Subtype.ext rfl

variable (Sp : IharaLemma.IdempotentSplitting (TT M Hs S 𝒪 k hcomm θbar))
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] k)
    (hπk : ∀ g : Gen M S, πk (Sp.toCornerRing i₀
      ⟨(hdata M Hs S 𝒪 k hcomm θbar).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M), ℓ ≡ 1 [MOD M] ∧
      θbar (Gen.T ℓ hℓ hℓS hℓM) ≠ (ℓ : k) + 1)

include hk hπk hEis in

theorem exists_nonEisenstein_elt :
    ∃ u : TT M Hs S 𝒪 k hcomm θbar, u ∉ Sp.𝔪 i₀ ∧ ∀ v : H1 M Hs 𝒪, u • v ∈ parR M Hs 𝒪 := by
  obtain ⟨ℓ, hℓ, hℓS, hℓM, h1, hne⟩ := hEis
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  letI : CommRing (Sp.CornerRing i₀) := cornerCommRing Sp i₀
  let u : TT M Hs S 𝒪 k hcomm θbar :=
    gen M Hs S 𝒪 k hcomm θbar (Gen.T ℓ hℓ hℓS hℓM) - algebraMap 𝒪 (TT M Hs S 𝒪 k hcomm θbar) ((ℓ : 𝒪) + 1)

  have hval : πk (Sp.toCornerRing i₀ u) = θbar (Gen.T ℓ hℓ hℓS hℓM) - ((ℓ : k) + 1) := by
    show πk (Sp.toCornerRing i₀ (gen M Hs S 𝒪 k hcomm θbar (Gen.T ℓ hℓ hℓS hℓM) -
      algebraMap 𝒪 (TT M Hs S 𝒪 k hcomm θbar) ((ℓ : 𝒪) + 1))) = _
    rw [map_sub (Sp.toCornerRing i₀), map_sub πk, hπk, toCornerRing_algebraMap, AlgHom.commutes,
      map_add, map_natCast, map_one]
  have hval_ne : πk (Sp.toCornerRing i₀ u) ≠ 0 := by
    rw [hval]
    exact sub_ne_zero.mpr hne
  refine ⟨u, ?_, ?_⟩
  ·
    rw [𝔪_eq_ker Sp i₀ hk πk, RingHom.mem_ker]
    exact hval_ne
  ·
    intro v
    have hmem := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one M Hs 𝒪 v ℓ hℓ hℓM h1
    rw [mem_parabolicHoms_iff] at hmem
    have huv : u • v = heckeT M Hs ℓ 𝒪 v - (ℓ + 1) • v := by
      show ((gen M Hs S 𝒪 k hcomm θbar (Gen.T ℓ hℓ hℓS hℓM) -
        algebraMap 𝒪 (TT M Hs S 𝒪 k hcomm θbar) ((ℓ : 𝒪) + 1) : TT M Hs S 𝒪 k hcomm θbar) :
          Module.End 𝒪 (H1 M Hs 𝒪)) v = _
      rw [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, LinearMap.sub_apply,
        Module.algebraMap_end_apply, add_smul, one_smul, Nat.cast_smul_eq_nsmul, add_smul, one_smul]
      rfl
    rw [huv]
    exact (mem_parabolicHoms_iff).mpr hmem

include hSfin hk hπk hEis in

theorem main :
    Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := H1 M Hs 𝒪) (Sp.e i₀)) =
      2 * Module.finrank 𝒪 (Sp.CornerRing i₀) := by

  obtain ⟨n, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree (GammaH M Hs)
  obtain ⟨b𝒪, hb𝒪⟩ := hb 𝒪
  obtain ⟨bC, hbC⟩ := hb ℂ

  have hD1 := descent M Hs S hSfin b bC hbC 𝒪

  obtain ⟨u, hu, huW⟩ := exists_nonEisenstein_elt M Hs S 𝒪 k hk hcomm θbar Sp i₀ πk hπk hEis
  have hW := TT_smul_mem M Hs S 𝒪 k hcomm θbar
  have hfaith := TT_faithful M Hs S 𝒪 k hcomm θbar
  have he : ∀ v : H1 M Hs 𝒪, Sp.e i₀ • v ∈ parR M Hs 𝒪 :=
    e_smul_mem 𝒪 Sp i₀ (parR M Hs 𝒪) hW hu huW

  set A : Subalgebra 𝒪 (Module.End 𝒪 ↥(parR M Hs 𝒪)) := (res M Hs S 𝒪 k hcomm θbar).range with hAdef
  have hAmat : A.map (ΦmH b𝒪) =
      Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪)) := by
    rw [hAdef, range_res M Hs S 𝒪 k hcomm θbar]
    exact map_adjoin_TparI b b𝒪 hb𝒪 S

  have hc := finrank_cornerSubmodule_eq 𝒪 Sp i₀ (parR M Hs 𝒪) hW he
  have hr := finrank_cornerRing_eq 𝒪 Sp i₀ (parR M Hs 𝒪) hW hfaith he
  set x : Module.End 𝒪 ↥(parR M Hs 𝒪) := res M Hs S 𝒪 k hcomm θbar (Sp.e i₀) with hxdef
  have hxA : x ∈ A := ⟨Sp.e i₀, rfl⟩
  have hxmem : Φm b𝒪 x ∈ Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪)) := by
    rw [← hAmat]
    exact Subalgebra.mem_map.mpr ⟨x, hxA, rfl⟩
  have hxidem : IsIdempotentElem (Φm b𝒪 x) := by
    have : IsIdempotentElem x := by
      show x * x = x
      rw [hxdef, ← map_mul, (Sp.idem i₀).eq]
    exact this.map _
  have h1 := hD1 _ hxmem hxidem
  rw [← hAmat, finrank_range_toLin'_Φm, finrank_range_mulLeft_Φm] at h1
  exact hc.trans (h1.trans (by rw [hr]))

end Assembly

end RANKGH
p2m_reactivate "P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_finrank_cornerRing_of_not_isEisenstein.RANKGH"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
open scoped IsMulCommutative in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ) (S : Finset ℕ)
    (hcomm : ∀ g h : CohCarrier.Gen M' ↑S,
      CohCarrier.opFamily M' H' ↑S 𝒪 g * CohCarrier.opFamily M' H' ↑S 𝒪 h =
        CohCarrier.opFamily M' H' ↑S 𝒪 h * CohCarrier.opFamily M' H' ↑S 𝒪 g)
    (θbar : CohCarrier.Gen M' ↑S → k)
    (S' : IharaLemma.IdempotentSplitting ↥(CohCarrier.hdata M' H' ↑S 𝒪 k hcomm θbar).opSubalgebra)
    (i₀' : Fin S'.n) (πk : S'.CornerRing i₀' →ₐ[𝒪] k)
    (hπk : ∀ g : CohCarrier.Gen M' ↑S, πk (S'.toCornerRing i₀'
      ⟨(CohCarrier.hdata M' H' ↑S 𝒪 k hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'), ℓ ≡ 1 [MOD M'] ∧
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ≠ (ℓ : k) + 1) :
    Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀')) =
      2 * Module.finrank 𝒪 (S'.CornerRing i₀') :=
  RANKGH.main M' H' (↑S) S.finite_toSet 𝒪 k hk hcomm θbar S' i₀' πk hπk hEis

end
p2m_reactivate "P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_finrank_cornerRing_of_not_isEisenstein.RANKGH"

end S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_finrank_cornerRing_of_not_isEisenstein
end P2MW
export P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_finrank_cornerRing_of_not_isEisenstein (solution)

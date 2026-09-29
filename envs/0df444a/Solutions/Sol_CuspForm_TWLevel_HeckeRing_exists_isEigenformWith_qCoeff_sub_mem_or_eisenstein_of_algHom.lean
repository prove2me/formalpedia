-- Prove2me | solution 1 for CuspForm.TWLevel.HeckeRing.exists_isEigenformWith_qCoeff_sub_mem_or_eisenstein_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3082264a-5fc5-5bb1-99e8-9a512edcebdf

import Definitions.Def_CuspForm_TWLevelHeckeRing
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_TWLevel_HeckeRing_OperatorAlgebra_exists_U_eigenvector_H1_of_algHom
import Theorems.Thm_CohCarrier_OperatorAlgebra_exists_isEigenformWith_qCoeff_eq_or_eisenstein_of_heckeT_eq_smul
import Theorems.Thm_CuspForm_IsEigenformWith_OperatorAlgebra_finite_adjoin_qCoeff
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_HeckeRing_exists_isEigenformWith_qCoeff_sub_mem_or_eisenstein_of_algHom
p2m_attr_erase "instance" "IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing CohCarrier.GammaHLower_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CuspForm.GammaH_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne"
p2m_attr_erase "simp" "CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.PeterssonCoset.mapGL_apply ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped MatrixGroups
p2m_open "IsLocalRing CuspForm.TWLevel P2MW.S_CuspForm_TWLevel_HeckeRing_exists_isEigenformWith_qCoeff_sub_mem_or_eisenstein_of_algHom.CuspForm.TWLevel Cardinal"

namespace CuspForm
p2m_export "CuspForm" "mk smul_apply ext TWLevel.HeckeRing heckeAlgebra IsEigenformWith TWLevel.HeckeRing.OperatorAlgebra.exists_U_eigenvector_H1_of_algHom IsEigenformWith.OperatorAlgebra.finite_adjoin_qCoeff"
namespace TWLevel
p2m_export "CuspForm.TWLevel" "HeckeRing HeckeRing.T HeckeRing.diamond level dvd_level_q HR OpComm DiaComm HeckeRing.OperatorAlgebra.exists_U_eigenvector_H1_of_algHom"
namespace HeckeRing
p2m_export "CuspForm.TWLevel.HeckeRing" "ext T diamond OperatorAlgebra.exists_U_eigenvector_H1_of_algHom"
namespace OperatorAlgebra
p2m_export "CuspForm.TWLevel.HeckeRing.OperatorAlgebra" "exists_U_eigenvector_H1_of_algHom"
namespace ClassicalityU
p2m_open "CuspForm.TWLevel.HeckeRing.OperatorAlgebra CuspForm.TWLevel.HeckeRing CuspForm.TWLevel CuspForm"

section Card

variable (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
  [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']

omit [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪'] in
theorem smul_top_pow (n : ℕ) :
    (maximalIdeal 𝒪' ^ n • ⊤ : Submodule 𝒪' 𝒪') = (maximalIdeal 𝒪' ^ n : Ideal 𝒪') := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

omit [CharZero 𝒪'] in
theorem mk_le_continuum : #𝒪' ≤ 𝔠 := by
  classical
  haveI : Finite (𝒪' ⧸ maximalIdeal 𝒪') := ‹Finite (ResidueField 𝒪')›
  have hfin : ∀ n : ℕ, Finite (𝒪' ⧸ maximalIdeal 𝒪' ^ n) := fun n =>
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  have hcount : ∀ n : ℕ, ∃ f : (𝒪' ⧸ maximalIdeal 𝒪' ^ n) → ℕ, Function.Injective f := fun n => by
    haveI := hfin n
    exact exists_injective_nat _
  choose f hf using hcount
  let Φ : 𝒪' → (ℕ → ℕ) := fun x n => f n (Ideal.Quotient.mk (maximalIdeal 𝒪' ^ n) x)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have hmem : ∀ n, x - y ∈ maximalIdeal 𝒪' ^ n := by
      intro n
      have h1 : f n (Ideal.Quotient.mk _ x) = f n (Ideal.Quotient.mk _ y) := congr_fun hxy n
      have h2 := hf n h1
      rw [Ideal.Quotient.eq] at h2
      exact h2
    have hx : x - y = 0 := by
      refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := maximalIdeal 𝒪') (M := 𝒪')) (x - y)
        fun n => ?_
      rw [SModEq.zero, smul_top_pow]
      exact hmem n
    exact sub_eq_zero.mp hx
  have h1 := Cardinal.mk_le_of_injective hΦ
  have h2 : #(ℕ → ℕ) = 𝔠 := by
    rw [Cardinal.mk_arrow, Cardinal.mk_nat, lift_aleph0, aleph0_power_aleph0]
  rwa [h2] at h1

omit [Finite (ResidueField 𝒪')] [CharZero 𝒪'] in
theorem continuum_le_mk : 𝔠 ≤ #𝒪' := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪'
  have hmax : maximalIdeal 𝒪' = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hpow : ∀ n : ℕ, (maximalIdeal 𝒪' ^ n • ⊤ : Submodule 𝒪' 𝒪') = Ideal.span {ϖ ^ n} := by
    intro n
    rw [smul_top_pow, hmax, Ideal.span_singleton_pow]
  let term : Set ℕ → ℕ → 𝒪' := fun s i => if i ∈ s then ϖ ^ i else 0
  let ps : Set ℕ → ℕ → 𝒪' := fun s n => ∑ i ∈ Finset.range n, term s i
  have hterm : ∀ (s : Set ℕ) (i m : ℕ), m ≤ i → term s i ∈ Ideal.span {ϖ ^ m} := by
    intro s i m hmi
    by_cases hi : i ∈ s
    · simp only [term, hi, if_true]
      exact Ideal.mem_span_singleton.mpr (pow_dvd_pow ϖ hmi)
    · simp only [term, hi, if_false]
      exact Ideal.zero_mem _
  have hcompat : ∀ (s : Set ℕ) {m n : ℕ}, m ≤ n →
      ps s m ≡ ps s n [SMOD (maximalIdeal 𝒪' ^ m • ⊤ : Submodule 𝒪' 𝒪')] := by
    intro s m n hmn
    rw [hpow, SModEq.sub_mem]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have : ps s m - ps s (n + 1) = (ps s m - ps s n) - term s n := by
        simp only [ps, Finset.sum_range_succ]; ring
      rw [this]
      exact Ideal.sub_mem _ ih (hterm s n m hmn)
  have hlim : ∀ s : Set ℕ, ∃ L : 𝒪', ∀ n, ps s n ≡ L [SMOD (maximalIdeal 𝒪' ^ n • ⊤ : Submodule 𝒪' 𝒪')] :=
    fun s => IsPrecomplete.prec' (ps s) (hcompat s)
  choose lim hlim using hlim
  have hinj : Function.Injective lim := by
    intro s s' hss'
    by_contra hne
    have hex : ∃ i, ¬ (i ∈ s ↔ i ∈ s') := by
      by_contra hall
      push Not at hall
      exact hne (Set.ext hall)
    let i₀ := Nat.find hex
    have hi₀ : ¬ (i₀ ∈ s ↔ i₀ ∈ s') := Nat.find_spec hex
    have hlt : ∀ i < i₀, (i ∈ s ↔ i ∈ s') := fun i hi => by
      have := Nat.find_min hex hi
      push Not at this
      exact this

    have hdiff : ps s (i₀ + 1) - ps s' (i₀ + 1) = term s i₀ - term s' i₀ := by
      simp only [ps, Finset.sum_range_succ]
      have : ∑ i ∈ Finset.range i₀, term s i = ∑ i ∈ Finset.range i₀, term s' i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [term, hlt i (Finset.mem_range.mp hi)]
      rw [this]; ring
    have hunit : term s i₀ - term s' i₀ = ϖ ^ i₀ ∨ term s i₀ - term s' i₀ = -(ϖ ^ i₀) := by
      by_cases h1 : i₀ ∈ s
      · have h2 : i₀ ∉ s' := fun h2 => hi₀ ⟨fun _ => h2, fun _ => h1⟩
        left; simp [term, h1, h2]
      · have h2 : i₀ ∈ s' := by
          by_contra h2; exact hi₀ ⟨fun h => absurd h h1, fun h => absurd h h2⟩
        right; simp [term, h1, h2]

    have hmod : ps s (i₀ + 1) - ps s' (i₀ + 1) ∈ Ideal.span {ϖ ^ (i₀ + 1)} := by
      have h1 := hlim s (i₀ + 1)
      have h2 := hlim s' (i₀ + 1)
      rw [hpow, SModEq.sub_mem] at h1 h2
      have h3 : ps s (i₀ + 1) - ps s' (i₀ + 1) = (ps s (i₀ + 1) - lim s) - (ps s' (i₀ + 1) - lim s') := by
        rw [hss']; ring
      rw [h3]
      exact Ideal.sub_mem _ h1 h2
    rw [hdiff] at hmod
    have hdvd : ϖ ^ (i₀ + 1) ∣ ϖ ^ i₀ := by
      rcases hunit with h | h
      · rw [h] at hmod; exact Ideal.mem_span_singleton.mp hmod
      · rw [h] at hmod; exact (dvd_neg.mp (Ideal.mem_span_singleton.mp hmod))
    have := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hdvd
    omega
  have := Cardinal.mk_le_of_injective hinj
  rwa [Cardinal.mk_set_nat] at this

theorem mk_algebraicClosure_eq :
    #(AlgebraicClosure (FractionRing 𝒪')) = 𝔠 := by
  haveI : Infinite 𝒪' := Infinite.of_injective _ Nat.cast_injective
  apply le_antisymm
  · have h1 := Algebra.IsAlgebraic.cardinalMk_le_max (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪'))
    have h2 : #(FractionRing 𝒪') ≤ #𝒪' := by
      have hs : Function.Surjective (fun p : 𝒪' × 𝒪' =>
          algebraMap 𝒪' (FractionRing 𝒪') p.1 / algebraMap 𝒪' (FractionRing 𝒪') p.2) := by
        intro z
        obtain ⟨x, y, -, h⟩ := IsFractionRing.div_surjective (A := 𝒪') z
        exact ⟨(x, y), h⟩
      have := Cardinal.mk_le_of_surjective hs
      rwa [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mul_eq_self (Cardinal.aleph0_le_mk 𝒪')] at this
    calc #(AlgebraicClosure (FractionRing 𝒪')) ≤ max #(FractionRing 𝒪') ℵ₀ := h1
      _ ≤ max #𝒪' ℵ₀ := max_le_max h2 le_rfl
      _ ≤ 𝔠 := max_le (mk_le_continuum 𝒪') aleph0_le_continuum
  · have hinj : Function.Injective (algebraMap 𝒪' (AlgebraicClosure (FractionRing 𝒪'))) := by
      rw [IsScalarTower.algebraMap_eq 𝒪' (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪'))]
      exact (algebraMap (FractionRing 𝒪') _).injective.comp (IsFractionRing.injective 𝒪' _)
    exact (continuum_le_mk 𝒪').trans (Cardinal.mk_le_of_injective hinj)

theorem nonempty_ringEquiv_complex : Nonempty (AlgebraicClosure (FractionRing 𝒪') ≃+* ℂ) := by
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ (Cardinal.eq.mp ?_)
  · rw [mk_algebraicClosure_eq]; exact aleph0_lt_continuum
  · rw [mk_algebraicClosure_eq, Cardinal.mk_complex]

end Card

section CoeffRing

theorem isLocalHom_and_finite_residueField (𝒪' : Type) [CommRing 𝒪'] [IsLocalRing 𝒪']
    [Finite (ResidueField 𝒪')] (𝒪₁ : Type) [CommRing 𝒪₁] [IsLocalRing 𝒪₁]
    [Algebra 𝒪' 𝒪₁] [Module.Finite 𝒪' 𝒪₁] [Algebra.IsIntegral 𝒪' 𝒪₁] :
    ∃ _ : IsLocalHom (algebraMap 𝒪' 𝒪₁), Finite (ResidueField 𝒪₁) := by
  classical
  have hcomap : (maximalIdeal 𝒪₁).comap (algebraMap 𝒪' 𝒪₁) = maximalIdeal 𝒪' := by
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝒪') (maximalIdeal 𝒪₁)
    exact IsLocalRing.eq_maximalIdeal this
  have hloc : IsLocalHom (algebraMap 𝒪' 𝒪₁) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hxu
    have hxm : x ∈ maximalIdeal 𝒪' := hxu
    rw [← hcomap, Ideal.mem_comap] at hxm
    exact hxm hx
  refine ⟨hloc, ?_⟩

  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := 𝒪') (M := 𝒪₁)

  let Ψ : (Fin n → ResidueField 𝒪') → ResidueField 𝒪₁ := fun c =>
    ∑ i, residue 𝒪₁ (algebraMap 𝒪' 𝒪₁ (Quotient.out (c i)) * g i)
  have hΨ : Function.Surjective Ψ := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hy : y ∈ Submodule.span 𝒪' (Set.range g) := by rw [hg]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪').mp hy
    refine ⟨fun i => residue 𝒪' (c i), ?_⟩
    show ∑ i, residue 𝒪₁ (algebraMap 𝒪' 𝒪₁ (Quotient.out (residue 𝒪' (c i))) * g i) =
      Ideal.Quotient.mk _ y
    rw [← hc]
    show _ = residue 𝒪₁ (∑ i, c i • g i)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul]
    congr 1

    have h1 : Quotient.out (residue 𝒪' (c i)) - c i ∈ maximalIdeal 𝒪' := by
      rw [← Ideal.Quotient.eq]
      exact Ideal.Quotient.mk_out _
    have h2 : algebraMap 𝒪' 𝒪₁ (Quotient.out (residue 𝒪' (c i)) - c i) ∈ maximalIdeal 𝒪₁ := by
      rw [← Ideal.mem_comap, hcomap]; exact h1
    rw [map_sub, ← Ideal.Quotient.eq] at h2
    exact h2
  haveI : Finite (Fin n → ResidueField 𝒪') := inferInstance
  exact Finite.of_surjective Ψ hΨ

variable (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
  [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']

theorem exists_coeffRing
    (F : Type) [Field F] [Algebra 𝒪' F] [Algebra (FractionRing 𝒪') F]
    [IsScalarTower 𝒪' (FractionRing 𝒪') F] [CharZero F]
    (A : Subalgebra ℤ ℂ) [Module.Finite ℤ A] (τ : ℂ →+* F) :
    ∃ (𝒪₁ : Type) (_ : CommRing 𝒪₁) (_ : IsDomain 𝒪₁) (_ : IsDiscreteValuationRing 𝒪₁)
      (_ : IsAdicComplete (maximalIdeal 𝒪₁) 𝒪₁) (_ : Finite (ResidueField 𝒪₁)) (_ : CharZero 𝒪₁)
      (_ : Algebra 𝒪' 𝒪₁) (_ : Module.Finite 𝒪' 𝒪₁) (_ : IsLocalHom (algebraMap 𝒪' 𝒪₁)),
      Function.Injective (algebraMap 𝒪' 𝒪₁) ∧
      ∃ (ι : A →+* 𝒪₁) (emb : 𝒪₁ →+* F), Function.Injective emb ∧
        (∀ x : A, emb (ι x) = τ x) ∧ ∀ y : 𝒪', emb (algebraMap 𝒪' 𝒪₁ y) = algebraMap 𝒪' F y := by
  classical
  set K' := FractionRing 𝒪' with hK'

  obtain ⟨sA, hsA⟩ := Module.Finite.fg_top (R := ℤ) (M := A)
  let τA : A →+* F := τ.comp A.val.toRingHom
  let gens : Set F := (fun x : A => τA x) '' (sA : Set A)
  haveI : Finite gens := (sA.finite_toSet.image _).to_subtype
  have hintZ : ∀ x : A, IsIntegral ℤ (τA x) := by
    intro x
    haveI : Algebra.IsIntegral ℤ A := Algebra.IsIntegral.of_finite ℤ A
    exact IsIntegral.map τA.toIntAlgHom (Algebra.IsIntegral.isIntegral x)
  have hintO : ∀ x : A, IsIntegral 𝒪' (τA x) := fun x => (hintZ x).tower_top
  have hintK : ∀ x : A, IsIntegral K' (τA x) := fun x => (hintO x).tower_top
  let K₁ : IntermediateField K' F := IntermediateField.adjoin K' gens
  haveI : FiniteDimensional K' K₁ := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨x, -, rfl⟩
    exact hintK x
  haveI : Algebra.IsSeparable K' K₁ := inferInstance

  have hmemK₁ : ∀ x : A, τA x ∈ K₁ := by
    intro x
    have hx : x ∈ Submodule.span ℤ (sA : Set A) := by rw [hsA]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K' gens ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem K₁
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul n y _ hy => rw [map_zsmul]; exact zsmul_mem hy n

  let 𝒪₁ : Type := ↥(integralClosure 𝒪' K₁)
  obtain ⟨hfin, hdvr, hcompl⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪' K' K₁
  haveI : Module.Finite 𝒪' 𝒪₁ := hfin
  haveI : IsDiscreteValuationRing 𝒪₁ := hdvr
  haveI : IsAdicComplete (maximalIdeal 𝒪₁) 𝒪₁ := hcompl
  obtain ⟨hloc, hfinres⟩ := isLocalHom_and_finite_residueField 𝒪' 𝒪₁

  let emb : 𝒪₁ →+* F := (algebraMap K₁ F).comp (algebraMap 𝒪₁ K₁)
  have hemb : ∀ z : 𝒪₁, emb z = ((z : K₁) : F) := fun z => rfl
  have hemb_inj : Function.Injective emb := by
    intro z w h
    rw [hemb, hemb] at h
    exact Subtype.ext (Subtype.ext h)
  have hemb_alg : ∀ y : 𝒪', emb (algebraMap 𝒪' 𝒪₁ y) = algebraMap 𝒪' F y := by
    intro y
    rw [hemb]
    show ((algebraMap 𝒪' K₁ y : K₁) : F) = algebraMap 𝒪' F y
    rw [IsScalarTower.algebraMap_apply 𝒪' K' K₁, IsScalarTower.algebraMap_apply 𝒪' K' F]
    rfl

  have hintK₁ : ∀ x : A, IsIntegral 𝒪' (⟨τA x, hmemK₁ x⟩ : K₁) := by
    intro x
    have hinj : Function.Injective ((IntermediateField.val K₁).restrictScalars 𝒪') :=
      (IntermediateField.val K₁).toRingHom.injective
    exact (isIntegral_algHom_iff ((IntermediateField.val K₁).restrictScalars 𝒪') hinj).mp (hintO x)
  let ι : A →+* 𝒪₁ :=
    { toFun := fun x => ⟨⟨τA x, hmemK₁ x⟩, hintK₁ x⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (by simp; rfl))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun x y => Subtype.ext (Subtype.ext (by simp; rfl)) }
  have hι : ∀ x : A, emb (ι x) = τ x := fun x => rfl
  refine ⟨𝒪₁, inferInstance, inferInstance, hdvr, hcompl, hfinres, inferInstance, inferInstance, hfin,
    hloc, ?_, ι, emb, hemb_inj, hι, hemb_alg⟩
  intro y z h
  have h1 := congrArg emb h
  rw [hemb_alg, hemb_alg] at h1
  exact (IsFractionRing.injective 𝒪' K') ((algebraMap K' F).injective (by
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]))

end CoeffRing

section Prelim

theorem algebraMap_injective_of_isLocalHom (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [Finite (ResidueField 𝒪)]
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [CharZero 𝒪'] [Algebra 𝒪 𝒪']
    [IsLocalHom (algebraMap 𝒪 𝒪')] : Function.Injective (algebraMap 𝒪 𝒪') := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖ0 : algebraMap 𝒪 𝒪' ϖ = 0 := by
    rw [map_mul, map_pow, mul_eq_zero] at hx
    rcases hx with h | h
    · exact absurd ((Units.map (algebraMap 𝒪 𝒪').toMonoidHom u).isUnit) (by rw [Units.coe_map]; simp [h])
    · exact eq_zero_of_pow_eq_zero h

  obtain ⟨p, hp⟩ := CharP.exists (ResidueField 𝒪)
  have hp0 : p ≠ 0 := CharP.char_ne_zero_of_finite (ResidueField 𝒪) p
  have hpm : (p : 𝒪) ∈ maximalIdeal 𝒪 := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (ResidueField 𝒪) p
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton] at hpm
  obtain ⟨y, hy⟩ := hpm
  have : (p : 𝒪') = 0 := by
    rw [← map_natCast (algebraMap 𝒪 𝒪'), hy, map_mul, hϖ0, zero_mul]
  exact hp0 (Nat.cast_eq_zero.mp this)

theorem isIntegral_dirichletCharacter_apply {L : ℕ} [NeZero L] (ψ : DirichletCharacter ℂ L)
    (u : (ZMod L)ˣ) : IsIntegral ℤ (ψ (u : ZMod L)) := by
  have hn : 0 < Fintype.card (ZMod L)ˣ := Fintype.card_pos
  have hpow : (ψ (u : ZMod L)) ^ Fintype.card (ZMod L)ˣ = 1 := by
    rw [← MulChar.coe_toUnitHom, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one,
      Units.val_one]
  refine ⟨Polynomial.X ^ Fintype.card (ZMod L)ˣ - 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hpow, sub_self]

theorem finite_adjoin_dirichlet {L : ℕ} [NeZero L] (ψ₁ ψ₂ : DirichletCharacter ℂ L) :
    Module.Finite ℤ ↥(Algebra.adjoin ℤ
      ((Set.range fun u : (ZMod L)ˣ => ψ₁ (u : ZMod L)) ∪
        Set.range fun u : (ZMod L)ˣ => ψ₂ (u : ZMod L))) := by
  refine Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_range _).union (Set.finite_range _)) ?_
  rintro _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
  · exact isIntegral_dirichletCharacter_apply ψ₁ u
  · exact isIntegral_dirichletCharacter_apply ψ₂ u

theorem heckeT_comp_ringHom {L : ℕ} (H : Subgroup (ZMod L)ˣ) {F : Type} [Field F]
    (g : F →+* ℂ) (ℓ : ℕ) [NeZero ℓ] (c : CohCarrier.H1 L H F) (x : F)
    (h : CohCarrier.heckeT L H ℓ F c = x • c) :
    CohCarrier.heckeT L H ℓ ℂ ((g : F →+ ℂ).comp c) = g x • (g : F →+ ℂ).comp c := by
  rw [CohCarrier.heckeT_comp_coeff, h]
  refine AddMonoidHom.ext fun γ => ?_
  show g ((x • c) γ) = g x * g (c γ)
  rw [AddMonoidHom.smul_apply, smul_eq_mul, map_mul]

theorem diamondL_comp_ringHom {L : ℕ} [NeZero L] (H : Subgroup (ZMod L)ˣ) {F : Type} [Field F]
    (g : F →+* ℂ) (u : (ZMod L)ˣ) (c : CohCarrier.H1 L H F) (x : F)
    (h : CohCarrier.diamondL L H F u c = x • c) :
    CohCarrier.diamondL L H ℂ u ((g : F →+ ℂ).comp c) = g x • (g : F →+ ℂ).comp c := by
  have : CohCarrier.diamondL L H ℂ u ((g : F →+ ℂ).comp c) =
      (g : F →+ ℂ).comp (CohCarrier.diamondL L H F u c) := rfl
  rw [this, h]
  refine AddMonoidHom.ext fun γ => ?_
  show g ((x • c) γ) = g x * g (c γ)
  rw [AddMonoidHom.smul_apply, smul_eq_mul, map_mul]

theorem heckeT_eq_of_eq {L : ℕ} (H : Subgroup (ZMod L)ˣ) {V : Type} [AddCommGroup V] {m n : ℕ}
    (hmn : m = n) [NeZero m] [NeZero n] (φ : CohCarrier.H1 L H V) :
    CohCarrier.heckeT L H m V φ = CohCarrier.heckeT L H n V φ := by
  subst hmn
  rfl

theorem mem_maximalIdeal_of_aeval_eq_zero {𝒪 𝒪' 𝒪₁ : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    [CommRing 𝒪'] [IsLocalRing 𝒪'] [CommRing 𝒪₁] [IsLocalRing 𝒪₁]
    [Algebra 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')] [Algebra 𝒪' 𝒪₁] [IsLocalHom (algebraMap 𝒪' 𝒪₁)]
    (P : Polynomial 𝒪) (hPm : P.Monic) (hPc : ∀ i < P.natDegree, P.coeff i ∈ maximalIdeal 𝒪)
    (x : 𝒪₁) (hx : Polynomial.aeval x (P.map (algebraMap 𝒪 𝒪')) = 0) : x ∈ maximalIdeal 𝒪₁ := by
  set n := P.natDegree with hn
  have hdeg : (P.map (algebraMap 𝒪 𝒪')).natDegree = n := hPm.natDegree_map _
  have hsum := hx
  rw [Polynomial.aeval_eq_sum_range, hdeg, Finset.sum_range_succ, Polynomial.coeff_map,
    show P.coeff n = 1 from hPm.coeff_natDegree, map_one, one_smul] at hsum

  have hpow : x ^ n ∈ maximalIdeal 𝒪₁ := by
    have h1 : x ^ n = -∑ i ∈ Finset.range n, (P.map (algebraMap 𝒪 𝒪')).coeff i • x ^ i :=
      eq_neg_of_add_eq_zero_right hsum
    rw [h1]
    refine (maximalIdeal 𝒪₁).neg_mem (Ideal.sum_mem _ fun i hi => ?_)
    rw [Polynomial.coeff_map, Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ ?_
    exact map_nonunit (algebraMap 𝒪' 𝒪₁) _
      (map_nonunit (algebraMap 𝒪 𝒪') _ (hPc i (Finset.mem_range.mp hi)))
  exact (IsLocalRing.maximalIdeal.isMaximal 𝒪₁).isPrime.mem_of_pow_mem n hpow

end Prelim

section Main

theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
    [Algebra 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
    (lam : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] 𝒪') :
    ∃ (𝒪₁ : Type) (_ : CommRing 𝒪₁) (_ : IsDomain 𝒪₁) (_ : IsDiscreteValuationRing 𝒪₁)
      (_ : IsAdicComplete (maximalIdeal 𝒪₁) 𝒪₁) (_ : Finite (ResidueField 𝒪₁)) (_ : CharZero 𝒪₁)
      (_ : Algebra 𝒪' 𝒪₁) (_ : Module.Finite 𝒪' 𝒪₁) (_ : IsLocalHom (algebraMap 𝒪' 𝒪₁)),
      Function.Injective (algebraMap 𝒪' 𝒪₁) ∧
      ((∃ (ε : DirichletCharacter ℂ (level N r qv))
          (h : CuspForm (CongruenceSubgroup.Gamma1 (level N r qv)) 2)
          (ι : Algebra.adjoin ℤ ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪
              Set.range fun u : (ZMod (level N r qv))ˣ => ε (u : ZMod (level N r qv))) →+* 𝒪₁),
          CuspForm.IsEigenformWith ε h ∧
          (∀ u : (ZMod (level N r qv))ˣ, u ∈ H → ε (u : ZMod (level N r qv)) = 1) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
            ι ⟨ModularFormClass.qCoeff h ℓ, Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL))) ∧
          (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
            ι ⟨ε (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu))) ∧
          (∀ (j : Fin t) (a : 𝒪), IsLocalRing.residue 𝒪 a = α j →
            ι ⟨ModularFormClass.qCoeff h (qv j), Algebra.subset_adjoin (Or.inl ⟨qv j, rfl⟩)⟩ -
                algebraMap 𝒪' 𝒪₁ (algebraMap 𝒪 𝒪' a) ∈ maximalIdeal 𝒪₁)) ∨
       (∃ (ψ₁ ψ₂ : DirichletCharacter ℂ (level N r qv))
          (ι : Algebra.adjoin ℤ
              ((Set.range fun u : (ZMod (level N r qv))ˣ => ψ₁ (u : ZMod (level N r qv))) ∪
                Set.range fun u : (ZMod (level N r qv))ˣ => ψ₂ (u : ZMod (level N r qv))) →+* 𝒪₁),
          (∀ u : (ZMod (level N r qv))ˣ, u ∈ H →
            ψ₁ (u : ZMod (level N r qv)) * ψ₂ (u : ZMod (level N r qv)) = 1) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
            ι ⟨ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) : ZMod (level N r qv)),
                Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)⟩ +
              (ℓ : 𝒪₁) * ι ⟨ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) :
                  ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL))) ∧
          (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
            ι ⟨ψ₁ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)⟩ *
                ι ⟨ψ₂ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu))))) := by
  classical

  let K' : Type := FractionRing 𝒪'
  let F : Type := AlgebraicClosure K'
  have htower : ∀ y : 𝒪, algebraMap 𝒪 F y = algebraMap 𝒪' F (algebraMap 𝒪 𝒪' y) := by
    intro y
    rw [IsScalarTower.algebraMap_apply 𝒪 K' F, IsScalarTower.algebraMap_apply 𝒪 𝒪' K',
      ← IsScalarTower.algebraMap_apply 𝒪' K' F]
  have hinjO'F : Function.Injective (algebraMap 𝒪' F) := by
    rw [IsScalarTower.algebraMap_eq 𝒪' K' F]
    exact (algebraMap K' F).injective.comp (IsFractionRing.injective 𝒪' K')
  have hF : Function.Injective (algebraMap 𝒪 F) := by
    have : (algebraMap 𝒪 F : 𝒪 → F) = algebraMap 𝒪' F ∘ algebraMap 𝒪 𝒪' := funext htower
    rw [this]
    exact hinjO'F.comp (algebraMap_injective_of_isLocalHom 𝒪 𝒪')
  let lam' : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] F :=
    { toRingHom := (algebraMap 𝒪' F).comp lam.toRingHom
      commutes' := fun y => by
        show algebraMap 𝒪' F (lam (algebraMap 𝒪 _ y)) = algebraMap 𝒪 F y
        rw [lam.commutes, htower] }
  have hlam' : ∀ x, lam' x = algebraMap 𝒪' F (lam x) := fun x => rfl

  obtain ⟨e, μ, c, hc0, hT, hUF, hD, hHR, hH, hres⟩ :=
    CuspForm.TWLevel.HeckeRing.OperatorAlgebra.exists_U_eigenvector_H1_of_algHom
      S N r θ t qv α H hc hdc F hF lam'

  obtain ⟨σ⟩ := nonempty_ringEquiv_complex 𝒪'
  let g : F →+* ℂ := σ.toRingHom
  let τ : ℂ →+* F := σ.symm.toRingHom
  have hτg : ∀ x : F, τ (g x) = x := fun x => σ.symm_apply_apply x
  let c' : CohCarrier.H1 (level N r qv) H ℂ := (g : F →+ ℂ).comp c
  have hc'0 : c' ≠ 0 := by
    intro h0
    apply hc0
    refine AddMonoidHom.ext fun γ => ?_
    have hγ : g (c γ) = 0 := DFunLike.congr_fun h0 γ
    apply σ.injective
    show g (c γ) = g 0
    rw [hγ, map_zero]
  let a : ℕ → ℂ := fun ℓ =>
    if h : ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ level N r qv then
      g (lam' (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ h.1 h.2.1 h.2.2)) else 0
  have ha : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      a ℓ = g (lam' (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL)) := by
    intro ℓ hℓ hℓS hℓL
    simp only [a, dif_pos (show ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ level N r qv from ⟨hℓ, hℓS, hℓL⟩)]

  let b : ℕ → ℂ := fun n =>
    if h : ∃ j : Fin t, qv j = n then g (μ (Classical.choose h)) else 0
  have hμeq : ∀ j j' : Fin t, qv j = qv j' → μ j = μ j' := by
    intro j j' hjj'
    have h1 := hUF j
    have h2 := hUF j'
    rw [heckeT_eq_of_eq H hjj' c, h2] at h1
    exact (smul_left_injective F hc0 h1).symm
  have hb : ∀ j : Fin t, b (qv j) = g (μ j) := by
    intro j
    have hex : ∃ j' : Fin t, qv j' = qv j := ⟨j, rfl⟩
    simp only [b, dif_pos hex]
    rw [hμeq (Classical.choose hex) j (Classical.choose_spec hex)]
  let Q : Set ℕ := Set.range qv
  have hQ : ∀ q ∈ Q, q ∣ level N r qv := by
    rintro _ ⟨j, rfl⟩
    exact dvd_level_q N r qv j
  let e' : (ZMod (level N r qv))ˣ →* ℂˣ := (Units.map (g : F →* ℂ)).comp e
  have he' : ∀ u, ((e' u : ℂˣ) : ℂ) = g ((e u : Fˣ) : F) := fun u => rfl
  have hT' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ level N r qv →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT (level N r qv) H ℓ ℂ c') = a ℓ • c' := by
    intro ℓ hℓ hℓS hℓL
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    rw [ha ℓ hℓ hℓS hℓL]
    exact heckeT_comp_ringHom H g ℓ c _ (hT ℓ hℓ hℓS hℓL)
  have hU' : ∀ (q : ℕ) (hq : q ∈ Q),
      (haveI : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne (level N r qv)) (hQ q hq)⟩;
        CohCarrier.heckeT (level N r qv) H q ℂ c') = b q • c' := by
    rintro _ ⟨j, rfl⟩
    rw [hb j]
    exact heckeT_comp_ringHom H g (qv j) c _ (hUF j)
  have hD' : ∀ u : (ZMod (level N r qv))ˣ,
      CohCarrier.diamondL (level N r qv) H ℂ u c' = ((e' u : ℂˣ) : ℂ) • c' := by
    intro u
    rw [he']
    exact diamondL_comp_ringHom H g u c _ (hD u)

  have hval_T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
      τ (a ℓ) = algebraMap 𝒪' F (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL)) := by
    intro ℓ hℓ hℓS hℓL
    rw [ha ℓ hℓ hℓS hℓL, hτg, hlam']
  have hval_dia : ∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
      τ ((e' u : ℂˣ) : ℂ) = algebraMap 𝒪' F (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu)) := by
    intro u hu
    rw [he', hτg, hHR u hu, hlam']
  have hval_H : ∀ u : (ZMod (level N r qv))ˣ, u ∈ H → ((e' u : ℂˣ) : ℂ) = 1 := by
    intro u hu
    rw [he', hH u hu, Units.val_one, map_one]
  have hval_U : ∀ j : Fin t, τ (b (qv j)) = μ j := by
    intro j
    rw [hb j, hτg]

  rcases CohCarrier.OperatorAlgebra.exists_isEigenformWith_qCoeff_eq_or_eisenstein_of_heckeT_eq_smul
      (level N r qv) H S Q hQ a b e' c' hc'0 hT' hU' hD' with
      ⟨ε, h, hh, hε, hqa, hqb⟩ | ⟨ψ₁, ψ₂, hψ, hqa⟩
  ·
    haveI := CuspForm.IsEigenformWith.OperatorAlgebra.finite_adjoin_qCoeff hh
    obtain ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj1, ι, emb, hemb, hιemb, hembalg⟩ :=
      exists_coeffRing 𝒪' F
        (Algebra.adjoin ℤ ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪
          Set.range fun u : (ZMod (level N r qv))ˣ => ε (u : ZMod (level N r qv)))) τ
    refine ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj1, Or.inl ⟨ε, h, ι, hh, ?_, ?_, ?_, ?_⟩⟩
    · intro u hu
      rw [hε u, hval_H u hu]
    · intro ℓ hℓ hℓS hℓL
      apply hemb
      rw [hιemb, hembalg, ← hval_T ℓ hℓ hℓS hℓL]
      show τ (ModularFormClass.qCoeff h ℓ) = τ (a ℓ)
      rw [hqa ℓ hℓ hℓS hℓL]
    · intro u hu
      apply hemb
      rw [hιemb, hembalg, ← hval_dia u hu]
      show τ (ε (u : ZMod (level N r qv))) = _
      rw [hε u]
    ·
      intro j a₀ ha₀
      obtain ⟨P, hPm, hPc, hP0⟩ := hres j a₀ ha₀
      apply mem_maximalIdeal_of_aeval_eq_zero (𝒪 := 𝒪) (𝒪' := 𝒪') P hPm hPc

      apply hemb
      have hembx : emb (ι ⟨ModularFormClass.qCoeff h (qv j), Algebra.subset_adjoin (Or.inl ⟨qv j, rfl⟩)⟩ -
          algebraMap 𝒪' 𝒪₁ (algebraMap 𝒪 𝒪' a₀)) = μ j - algebraMap 𝒪 F a₀ := by
        rw [map_sub, hιemb, hembalg, ← htower, ← hval_U j]
        show τ (ModularFormClass.qCoeff h (qv j)) - _ = _
        rw [hqb (qv j) ⟨j, rfl⟩]
      have hcomp : emb.comp (algebraMap 𝒪' 𝒪₁) = algebraMap 𝒪' F := RingHom.ext hembalg
      rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.eval₂_map, hembx,
        show (algebraMap 𝒪' F).comp (algebraMap 𝒪 𝒪') = algebraMap 𝒪 F from
          RingHom.ext fun y => (htower y).symm]
      exact hP0
  ·
    haveI := finite_adjoin_dirichlet ψ₁ ψ₂
    obtain ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj1, ι, emb, hemb, hιemb, hembalg⟩ :=
      exists_coeffRing 𝒪' F
        (Algebra.adjoin ℤ ((Set.range fun u : (ZMod (level N r qv))ˣ => ψ₁ (u : ZMod (level N r qv))) ∪
          Set.range fun u : (ZMod (level N r qv))ˣ => ψ₂ (u : ZMod (level N r qv)))) τ
    refine ⟨𝒪₁, i1, i2, i3, i4, i5, i6, i7, i8, i9, hinj1, Or.inr ⟨ψ₁, ψ₂, ι, ?_, ?_, ?_⟩⟩
    · intro u hu
      rw [hψ u, hval_H u hu]
    · intro ℓ hℓ hℓS hℓL
      apply hemb
      rw [map_add, map_mul, map_natCast emb, hιemb, hιemb, hembalg, ← hval_T ℓ hℓ hℓS hℓL,
        ← hqa ℓ hℓ hℓS hℓL]
      show τ (ψ₁ _) + (ℓ : F) * τ (ψ₂ _) = τ (ψ₁ (ℓ : ZMod (level N r qv)) + (ℓ : ℂ) * ψ₂ (ℓ : ZMod (level N r qv)))
      rw [ZMod.coe_unitOfCoprime, map_add, map_mul, map_natCast τ]
    · intro u hu
      apply hemb
      rw [map_mul, hιemb, hιemb, hembalg, ← hval_dia u hu, ← hψ u]
      show τ (ψ₁ _) * τ (ψ₂ _) = τ (ψ₁ (u : ZMod (level N r qv)) * ψ₂ (u : ZMod (level N r qv)))
      rw [map_mul]

end Main

end CuspForm.TWLevel.HeckeRing.OperatorAlgebra.ClassicalityU

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (S : Set ℕ) (N : ℕ) [NeZero N] (r : ℕ) [NeZero r]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (α : Fin t → ResidueField 𝒪)
    (H : Subgroup (ZMod (level N r qv))ˣ)
    (hc : OpComm N r qv S 𝒪 H) (hdc : DiaComm N r qv S 𝒪 H)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
    [Algebra 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
    (lam : HeckeRing N r qv S 𝒪 H θ α hc hdc →ₐ[𝒪] 𝒪') :
    ∃ (𝒪₁ : Type) (_ : CommRing 𝒪₁) (_ : IsDomain 𝒪₁) (_ : IsDiscreteValuationRing 𝒪₁)
      (_ : IsAdicComplete (maximalIdeal 𝒪₁) 𝒪₁) (_ : Finite (ResidueField 𝒪₁)) (_ : CharZero 𝒪₁)
      (_ : Algebra 𝒪' 𝒪₁) (_ : Module.Finite 𝒪' 𝒪₁) (_ : IsLocalHom (algebraMap 𝒪' 𝒪₁)),
      Function.Injective (algebraMap 𝒪' 𝒪₁) ∧
      ((∃ (ε : DirichletCharacter ℂ (level N r qv))
          (h : CuspForm (CongruenceSubgroup.Gamma1 (level N r qv)) 2)
          (ι : Algebra.adjoin ℤ ((Set.range fun n : ℕ => ModularFormClass.qCoeff h n) ∪
              Set.range fun u : (ZMod (level N r qv))ˣ => ε (u : ZMod (level N r qv))) →+* 𝒪₁),
          CuspForm.IsEigenformWith ε h ∧
          (∀ u : (ZMod (level N r qv))ˣ, u ∈ H → ε (u : ZMod (level N r qv)) = 1) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
            ι ⟨ModularFormClass.qCoeff h ℓ, Algebra.subset_adjoin (Or.inl ⟨ℓ, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL))) ∧
          (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
            ι ⟨ε (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu))) ∧
          (∀ (j : Fin t) (a : 𝒪), IsLocalRing.residue 𝒪 a = α j →
            ι ⟨ModularFormClass.qCoeff h (qv j), Algebra.subset_adjoin (Or.inl ⟨qv j, rfl⟩)⟩ -
                algebraMap 𝒪' 𝒪₁ (algebraMap 𝒪 𝒪' a) ∈ maximalIdeal 𝒪₁)) ∨
       (∃ (ψ₁ ψ₂ : DirichletCharacter ℂ (level N r qv))
          (ι : Algebra.adjoin ℤ
              ((Set.range fun u : (ZMod (level N r qv))ˣ => ψ₁ (u : ZMod (level N r qv))) ∪
                Set.range fun u : (ZMod (level N r qv))ˣ => ψ₂ (u : ZMod (level N r qv))) →+* 𝒪₁),
          (∀ u : (ZMod (level N r qv))ˣ, u ∈ H →
            ψ₁ (u : ZMod (level N r qv)) * ψ₂ (u : ZMod (level N r qv)) = 1) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ level N r qv),
            ι ⟨ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) : ZMod (level N r qv)),
                Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)⟩ +
              (ℓ : 𝒪₁) * ι ⟨ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) :
                  ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.T N r qv S 𝒪 H θ α hc hdc ℓ hℓ hℓS hℓL))) ∧
          (∀ (u : (ZMod (level N r qv))ˣ) (hu : u ∈ HR N r qv),
            ι ⟨ψ₁ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)⟩ *
                ι ⟨ψ₂ (u : ZMod (level N r qv)), Algebra.subset_adjoin (Or.inr ⟨u, rfl⟩)⟩ =
              algebraMap 𝒪' 𝒪₁ (lam (HeckeRing.diamond N r qv S 𝒪 H θ α hc hdc u hu))))) :=
  CuspForm.TWLevel.HeckeRing.OperatorAlgebra.ClassicalityU.main S N r θ t qv α H hc hdc 𝒪' lam

end S_CuspForm_TWLevel_HeckeRing_exists_isEigenformWith_qCoeff_sub_mem_or_eisenstein_of_algHom
end P2MW
export P2MW.S_CuspForm_TWLevel_HeckeRing_exists_isEigenformWith_qCoeff_sub_mem_or_eisenstein_of_algHom (solution)

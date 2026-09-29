-- Prove2me | solution 1 for CuspForm.heckeLocal.apply_eq_pi_U_of_forall_point_apply_eq_qCoeff_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/061917a9-82b2-50f7-8abe-bf2dac441630

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_CuspForm_heckeLocal_exists_points_jointly_injective_of_charpoly_frobenius_eq_of_isAbsolutelyIrreducible
import Theorems.Thm_CuspForm_exists_isNewform_of_point_of_up_dvd
import Theorems.Thm_CuspForm_apply_U_eq_intCast_of_point_of_not_isUnramifiedAt
import Theorems.Thm_CuspForm_heckeLocal_isLocalHom_and_residue_apply_pi
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq
import Theorems.Thm_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_qCoeff_of_isAbsolutelyIrreducible
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 TateModule.instModule TateModule.instSMul ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow HeckeEis.instFiniteProjLineCusps ModularCurve.numberField_of_finiteDimensional"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_heckeULowerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one"
p2m_attr_erase "simp" "AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk HeckeEis.coe_linePow ModularCurve.symPoly_zero"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace Ws24E1

theorem conj_mem_map_subtype {G : Type} [Group G] {D : Subgroup G} {I : Subgroup ↥D} (hI : I.Normal)
    {σ τ : G} (hσ : σ ∈ D) (hτ : τ ∈ I.map D.subtype) : σ * τ * σ⁻¹ ∈ I.map D.subtype := by
  obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.1 hτ
  exact Subgroup.mem_map.2 ⟨⟨σ, hσ⟩ * τ' * ⟨σ, hσ⟩⁻¹, hI.conj_mem τ' hτ' ⟨σ, hσ⟩, rfl⟩

theorem exists_frobenius_endo_inertiaCoinvariants {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (q : ℕ) (hq : q.Prime) :
    ∃ (P : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[k]
              (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1))),
      P.LiesOverPrime q ∧ P.IsFrobeniusAt σ q ∧
        ∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v) := by
  obtain ⟨P, σ, hP, hσ⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨q, hq⟩
  have hσD : σ ∈ P.decompositionSubgroup ℚ := hσ.mem_decompositionSubgroup
  have hNormal : (P.inertiaSubgroup ℚ).Normal := by
    unfold ValuationSubring.inertiaSubgroup; infer_instance
  have hinv : ∀ w : ρbar.V, ρbar.ρ σ⁻¹ (ρbar.ρ σ w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hle : (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) ≤
      (⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)).comap (ρbar.ρ σ) := by
    refine iSup₂_le fun τ hτ => ?_
    rintro _ ⟨v, rfl⟩
    have hτ' : τ ∈ (P.inertiaSubgroup ℚ).map (P.decompositionSubgroup ℚ).subtype := hτ
    have hconj : σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ := conj_mem_map_subtype hNormal hσD hτ'
    have key : ρbar.ρ σ ((ρbar.ρ τ - 1) v) = (ρbar.ρ (σ * τ * σ⁻¹) - 1) (ρbar.ρ σ v) := by
      rw [map_mul, map_mul, LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
        Module.End.mul_apply, Module.End.mul_apply, hinv, map_sub]
    rw [Submodule.mem_comap, key]
    exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hconj (LinearMap.mem_range_self _ _))
  exact ⟨P, σ, Submodule.mapQ _ _ (ρbar.ρ σ) hle, hP, hσ, fun v => rfl⟩

end Ws24E1

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S S₀ : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S) (hS₀ : S₀ ⊆ S)
    (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (hNS₀ : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S₀) (hNp : ¬ p ^ 2 ∣ N)
    (hunr : ∀ q ∈ S, q ≠ p → ¬ q ∣ N → ρbar.IsUnramifiedAt q)
    (hst : ∀ q : ℕ, q.Prime → q ≠ p → q ∣ N → ¬ q ^ 2 ∣ N →
      ¬ ρbar.IsUnramifiedAt q ∧ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (hsq : ∀ q : ℕ, q.Prime → q ≠ p → q ^ 2 ∣ N →
      ¬ q ^ 3 ∣ N ∧ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (hord : p ∣ N → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ' : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* ResidueField 𝒪)

    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₀ : ℓ ∉ (↑S₀ : Set ℕ)), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀)) * X + C (ℓ : ResidueField 𝒪))

    (hU0 : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)), q ^ 2 ∣ N →
      θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = 0)

    (hU1 : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)), ¬ q ^ 2 ∣ N →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
          ∀ E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[ResidueField 𝒪]
              (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)),
            (∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) →
              θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = LinearMap.trace (ResidueField 𝒪) _ E)

    (hTp : ∀ (hpN : ¬ p ∣ N) (hpS₀ : p ∉ (↑S₀ : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
          ∀ E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[ResidueField 𝒪]
              (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)),
            (∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) →
              θ' (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpN hpS₀) =
                LinearMap.trace (ResidueField 𝒪) _ E)

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
      θ t = θ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))
    (Ψ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] CuspForm.heckeLocal N (↑S₀ : Set ℕ) 𝒪 θ')
    (hΨ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
      Ψ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ t) =
        CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ'
          (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hq2 : ¬ q ^ 2 ∣ N)
    (u : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ)
    (hu : ∀ (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
        [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
        [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
        (ψ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] 𝒪')
        (M : ℕ) [NeZero M] (hMN : M ∣ N)
        (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), g.IsNewform →
        ∀ (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ),
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ) →
        ∀ (iota : chig.range →+* 𝒪'),
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
              (fun h => hℓN (h.trans hMN)) hℓS)) =
              ψ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) →
        q ∣ M ∧ ∃ a : ℤ, (a = 1 ∨ a = -1) ∧
          ModularFormClass.qCoeff g q = (a : ℂ) ∧ ψ u = (a : 𝒪')) :
    Ψ u = CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ'
      (CuspForm.heckeAlgebra.U hq hqN (hNS₀ q hq hqN)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI hqF : Fact q.Prime := ⟨hq⟩
  have hqS₀ : q ∉ (↑S₀ : Set ℕ) := hNS₀ q hq hqN
  have hqS : q ∈ S := hNS q hq hqN

  obtain ⟨n, A, hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, χ, hχloc, hinj⟩ :=
    CuspForm.heckeLocal.exists_points_jointly_injective_of_charpoly_frobenius_eq_of_isAbsolutelyIrreducible
      p hp2 hp𝒪 ρbar habs S S₀ hS hpS hS₀ N hNS hNS₀ hNp hunr hst hsq hord θ' hT hU0 hU1 hTp

  suffices key : ∀ i, χ i (Ψ u) =
      χ i (CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀)) by
    have h0 := hinj (Ψ u - CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ'
        (CuspForm.heckeAlgebra.U hq hqN hqS₀)) fun i => by rw [map_sub, key i, sub_self]
    exact sub_eq_zero.mp h0
  intro i
  letI := hA1 i; letI := hA2 i; letI := hA3 i; letI := hA4 i; letI := hA5 i
  letI := hA6 i; letI := hA7 i; letI := hA8 i; letI := hA9 i
  have hS₀S : (↑S₀ : Set ℕ) ⊆ (↑S : Set ℕ) := Finset.coe_subset.mpr hS₀
  have hS₀Sq : (↑S₀ : Set ℕ) ⊆ (↑S : Set ℕ) \ {q} := fun x hx =>
    ⟨hS₀S hx, fun hxq => hqS₀ ((Set.mem_singleton_iff.mp hxq) ▸ hx)⟩

  obtain ⟨χfull, hχfull⟩ : ∃ χfull : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* A i,
      ∀ t, χfull t = χ i (CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ' t) :=
    ⟨(χ i).toRingHom.comp (CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ'), fun _ => rfl⟩
  obtain ⟨χS, hχS⟩ : ∃ χS : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* A i,
      ∀ t, χS t = χfull (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS₀S) t) :=
    ⟨χfull.comp (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS₀S)).toRingHom, fun _ => rfl⟩
  obtain ⟨χSq, hχSq⟩ : ∃ χSq : CuspForm.heckeAlgebra N 2 ((↑S : Set ℕ) \ {q}) →+* A i,
      ∀ t, χSq t = χfull (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS₀Sq) t) :=
    ⟨χfull.comp (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS₀Sq)).toRingHom, fun _ => rfl⟩
  have hχSqS : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
      χSq (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono Set.diff_subset) t) = χS t := by
    intro t
    rw [hχSq, hχS, Subalgebra.inclusion_inclusion]
  obtain ⟨up, hup_def⟩ : ∃ up : A i, up = χfull (CuspForm.heckeAlgebra.U hq hqN hqS₀) := ⟨_, rfl⟩
  have hχSqU : χSq (CuspForm.heckeAlgebra.U (Fact.out : q.Prime) hqN (by simp)) = up := by
    rw [hχSq, hup_def]
    congr 1

  have hres : ∀ t, residue (A i) (χfull t) = ResidueField.map (algebraMap 𝒪 (A i)) (θ' t) := by
    intro t
    rw [hχfull]
    exact (CuspForm.heckeLocal.isLocalHom_and_residue_apply_pi N (↑S₀ : Set ℕ) 𝒪 θ' (χ i)).2 t

  have hdvd : up ∣ (q : A i) := by
    by_cases hqp : q = p
    ·
      subst hqp
      have hdetc : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic q := by
        refine GaloisRepAdic.detIsCyclotomic_of_forall_frobenius_det_eq
          (GaloisRepAdic.ofResidualGaloisRep ρbar) hq ?_ S ?_
        · have h0 : (q : ResidueField 𝒪) = 0 := by
            rw [← map_natCast (residue 𝒪), residue_eq_zero_iff]; exact hp𝒪
          rw [h0]; exact Ideal.zero_mem _
        · intro ℓ hℓ hℓS B τ hB hτ
          have hℓS' : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS (Finset.mem_coe.mp h)
          have hℓN : ¬ ℓ ∣ N := fun h => hℓS (hNS ℓ hℓ h)
          have hℓS₀ : ℓ ∉ (↑S₀ : Set ℕ) := fun h => hℓS' (hS₀S h)
          have hℓq : ℓ ≠ q := fun h => hℓS (h ▸ hpS)
          have hcp := hT ℓ hℓ hℓN hℓS₀ hℓq B hB τ hτ
          show LinearMap.det (ρbar.ρ τ) = (ℓ : ResidueField 𝒪)
          have hd := LinearMap.det_eq_sign_charpoly_coeff (ρbar.ρ τ)
          rw [hcp, ρbar.finrank_eq] at hd
          rw [hd]
          simp [coeff_C, coeff_X]
      obtain ⟨P, σ, E, hP, hσ, hE⟩ := Ws24E1.exists_frobenius_endo_inertiaCoinvariants ρbar q hq
      have htr := ResidualGaloisRep.trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
        q hp2 ρbar hdetc (hord hqN) P hP σ E hE
      have hθU : θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) ≠ 0 := by
        rw [hU1 q hq hqN hqS₀ hq2 P hP σ hσ E hE]; exact htr
      have hunit : IsUnit up := by
        rw [hup_def, ← residue_ne_zero_iff_isUnit, hres]
        exact (map_ne_zero (ResidueField.map (algebraMap 𝒪 (A i)))).mpr hθU
      exact hunit.dvd
    ·
      obtain ⟨a', ha', hupa⟩ :=
        CuspForm.apply_U_eq_intCast_of_point_of_not_isUnramifiedAt p hp𝒪 ρbar habs N S S₀ hS₀ hS hpS
          hNS hNS₀ θ'
          (fun ℓ hℓ hℓN hℓS P hP σ hσ =>
            hT ℓ hℓ hℓN _ (fun h => hℓS (h ▸ Finset.mem_coe.mpr hpS)) P hP σ hσ)
          (A i) χfull hres q hq hqp hqN hq2 (hst q hq hqp hqN hq2).1
      have hunit : IsUnit up := by
        rw [hup_def, hupa]
        rcases ha' with rfl | rfl <;> simp
      exact hunit.dvd

  obtain ⟨Mg, hMg0, hMgN, g, hg, chig, hchigT, hchigU, iota, hiotaT, hdich⟩ :=
    CuspForm.exists_isNewform_of_point_of_up_dvd q N S hNS (A i) χS hqN up
      ⟨χSq, hχSqS, hχSqU⟩ hdvd
  haveI := hMg0

  obtain ⟨chig₀, hchig₀def⟩ : ∃ chig₀ : CuspForm.heckeAlgebra Mg 2 (↑S : Set ℕ) →+* ℂ,
      ∀ t, chig₀ t = chig (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono Set.diff_subset) t) :=
    ⟨chig.comp (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono Set.diff_subset)).toRingHom, fun _ => rfl⟩
  have hchig₀T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ Mg) (hℓS : ℓ ∉ (↑S : Set ℕ))
      (hℓSq : ℓ ∉ (↑S : Set ℕ) \ {q}),
      chig₀ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓSq) := by
    intro ℓ hℓ hℓM hℓS hℓSq
    rw [hchig₀def]
    congr 1
  have hchig₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ Mg) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig₀ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ := by
    intro ℓ hℓ hℓM hℓS
    rw [hchig₀T ℓ hℓ hℓM hℓS (fun h => hℓS h.1), hchigT]
  have hrange : chig₀.range ≤ chig.range := by
    rintro _ ⟨x, rfl⟩
    rw [hchig₀def]
    exact RingHom.mem_range.mpr ⟨_, rfl⟩
  obtain ⟨iota₀, hiota₀def⟩ : ∃ iota₀ : chig₀.range →+* A i, ∀ y, iota₀ y = iota (Subring.inclusion hrange y) :=
    ⟨iota.comp (Subring.inclusion hrange), fun _ => rfl⟩
  have hiota₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      iota₀ (chig₀.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN)) hℓS)) =
        ((χ i).comp Ψ) (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := by
    intro ℓ hℓ hℓN hℓS
    rw [hiota₀def, AlgHom.comp_apply, hΨ, ← hχfull, ← hχS, ← hiotaT ℓ hℓ hℓN hℓS]
    congr 1
    apply Subtype.ext
    show chig₀ (CuspForm.heckeAlgebra.T hℓ _ hℓS) = chig (CuspForm.heckeAlgebra.T hℓ _ _)
    exact hchig₀T ℓ hℓ _ hℓS _
  obtain ⟨hqMg, a, ha, hgq, hψu⟩ :=
    hu (A i) ((χ i).comp Ψ) Mg hMgN g hg chig₀ hchig₀ iota₀ hiota₀

  rcases hdich with ⟨hnot, -⟩ | ⟨hqMg', -, hiotaU⟩
  · exact absurd hqMg hnot
  have hval : chig.rangeRestrict (CuspForm.heckeAlgebra.U (Fact.out : q.Prime) hqMg' (by simp)) =
      ((a : ℤ) : chig.range) := by
    apply Subtype.ext
    rw [RingHom.coe_rangeRestrict, hchigU hqMg', hgq]
    simp
  have hup : up = (a : A i) := by rw [← hiotaU, hval, map_intCast]

  calc χ i (Ψ u) = ((χ i).comp Ψ) u := rfl
    _ = (a : A i) := hψu
    _ = up := hup.symm
    _ = χfull (CuspForm.heckeAlgebra.U hq hqN hqS₀) := hup_def
    _ = χ i (CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀)) := hχfull _

end S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_qCoeff_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_qCoeff_of_isAbsolutelyIrreducible (solution)

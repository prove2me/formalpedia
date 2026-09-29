-- Prove2me | solution 1 for CuspForm.heckeLocal.isReduced_of_charpoly_frobenius_eq_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9c45f40b-d7f9-5d61-9583-2b8ca3830d67

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_CuspForm_heckeLocal_adjoin_range_pi
import Theorems.Thm_CuspForm_isReduced_heckeAlgebra_of_primeFactors_subset
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CuspForm_heckeLocal_pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd
import Theorems.Thm_CuspForm_heckeAlgebra_exists_apply_ne_zero_and_mul_U_sq_sub_one_eq_zero_of_not_isUnramifiedAt
import Theorems.Thm_CuspForm_heckeAlgebra_exists_apply_ne_zero_and_squarefree_and_mul_aeval_U_eq_zero_of_apply_U_ne_zero
import Theorems.Thm_ResidualGaloisRep_trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_of_forall_frobenius_det_eq
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_isReduced_of_charpoly_frobenius_eq_of_isAbsolutelyIrreducible
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
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Polynomial IsLocalRing
open scoped TensorProduct

namespace RFMain

section Part1

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
  {T : Type} [CommRing T] [Algebra 𝒪 T] [Module.Free 𝒪 T] [Module.Finite 𝒪 T]

theorem isReduced_of_free_of_adjoin_eq_top (G : Set T) (hadj : Algebra.adjoin 𝒪 G = ⊤)
    (hG : ∀ g ∈ G, ∃ P : ℤ[X], Squarefree (P.map (Int.castRingHom ℚ)) ∧ aeval g P = 0) :
    IsReduced T := by
  classical
  let K := FractionRing 𝒪
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  let ι := Module.Free.ChooseBasisIndex 𝒪 T
  let b : Module.Basis ι 𝒪 T := Module.Free.chooseBasis 𝒪 T

  let Φ : T →ₐ[𝒪] Matrix ι ι K :=
    ((Algebra.ofId 𝒪 K).mapMatrix.comp
      (LinearMap.toMatrixAlgEquiv b : Module.End 𝒪 T ≃ₐ[𝒪] Matrix ι ι 𝒪).toAlgHom).comp
      (Algebra.lmul 𝒪 T)
  have hΦ : Function.Injective Φ := by
    refine (Matrix.map_injective (IsFractionRing.injective 𝒪 K)).comp
      ((LinearMap.toMatrixAlgEquiv b).injective.comp (Algebra.lmul_injective (R := 𝒪) (A := T)))

  let Ψ : T →+* Module.End K (ι → K) :=
    (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).toRingEquiv.toRingHom.comp
      Φ.toRingHom
  have hΨ : ∀ x, Ψ x = Matrix.toLin' (Φ x) := fun x => rfl
  have hΨinj : Function.Injective Ψ :=
    (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K)).injective.comp hΦ

  have hΨc : ∀ x y, Commute (Ψ x) (Ψ y) := fun x y => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hss : ∀ x, (Ψ x).IsSemisimple := by
    intro x
    have hx : x ∈ Algebra.adjoin 𝒪 G := hadj ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem g hg =>
      obtain ⟨P, hP, hP0⟩ := hG g hg
      refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
        (p := P.map (Int.castRingHom K)) ?_ ?_
      · rw [← PerfectField.separable_iff_squarefree] at hP ⊢
        have := hP.map (f := algebraMap ℚ K)
        rwa [Polynomial.map_map, RingHom.eq_intCast' ((algebraMap ℚ K).comp (Int.castRingHom ℚ))]
          at this
      · have h2 : aeval (Ψ g) P = Ψ.toIntAlgHom (aeval g P) :=
          (Polynomial.aeval_algHom_apply Ψ.toIntAlgHom g P)
        rw [aeval_def, eval₂_map, RingHom.ext_int ((algebraMap K _).comp (Int.castRingHom K))
          (algebraMap ℤ _), ← aeval_def, h2, hP0, map_zero]
    | algebraMap r =>
      have : Ψ (algebraMap 𝒪 T r) = algebraMap 𝒪 K r • (1 : Module.End K (ι → K)) := by
        rw [hΨ, AlgHom.commutes, IsScalarTower.algebraMap_apply 𝒪 K (Matrix ι ι K),
          Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
      rw [this]
      exact Module.End.IsSemisimple_smul _ Module.End.isSemisimple_id
    | add x y _ _ hx hy => rw [map_add]; exact hx.add_of_commute (hΨc x y) hy
    | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul_of_commute (hΨc x y) hy
  refine ⟨fun x hx => hΨinj ?_⟩
  rw [map_zero]
  exact Module.End.eq_zero_of_isNilpotent_isSemisimple (hx.map Ψ) (hss x)

end Part1

section Part2

variable {A : Type} [CommRing A] [IsReduced A]

theorem squarefree_map_minpoly_of_isReduced (t : A) (ht : IsIntegral ℤ t) :
    Squarefree ((minpoly ℤ t).map (Int.castRingHom ℚ)) := by
  classical
  nontriviality A
  set P := minpoly ℤ t with hPdef
  have hPm : P.Monic := minpoly.monic ht
  have hmapeq : (Int.castRingHom ℚ) = algebraMap ℤ ℚ := RingHom.eq_intCast' _ |>.symm
  rw [hmapeq]
  intro g hg
  by_contra hgu
  have hPQ0 : P.map (algebraMap ℤ ℚ) ≠ 0 := (hPm.map _).ne_zero
  have hg0 : g ≠ 0 := fun h => hPQ0 (by
    obtain ⟨s, hs⟩ := hg; rw [hs, h, zero_mul, zero_mul])

  set g₁ := g * C (leadingCoeff g)⁻¹ with hg₁
  have hg₁m : g₁.Monic := monic_mul_leadingCoeff_inv hg0
  have hg₁g : Associated g₁ g :=
    (associated_mul_isUnit_left_iff (isUnit_C.mpr
      (inv_ne_zero (leadingCoeff_ne_zero.mpr hg0)).isUnit)).mpr (Associated.refl g) |>.symm.symm
  have hdvd : g₁ * g₁ ∣ P.map (algebraMap ℤ ℚ) :=
    (Associated.dvd_iff_dvd_left (hg₁g.mul_mul hg₁g)).mpr hg
  obtain ⟨s, hs⟩ := hdvd

  obtain ⟨a, ha⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hPm
    (⟨g₁ * s, by rw [hs, mul_assoc]⟩ : g₁ ∣ P.map (algebraMap ℤ ℚ))
  rw [hg₁m.leadingCoeff, C_1, mul_one] at ha
  have hsm : s.Monic := by
    have := (hPm.map (algebraMap ℤ ℚ)).leadingCoeff
    rw [hs, leadingCoeff_mul, leadingCoeff_mul, hg₁m.leadingCoeff, one_mul, one_mul] at this
    exact this
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (K := ℚ) hPm
    (⟨g₁ * g₁, by rw [hs, mul_comm]⟩ : s ∣ P.map (algebraMap ℤ ℚ))
  rw [hsm.leadingCoeff, C_1, mul_one] at hc
  have ham : a.Monic := monic_of_injective (algebraMap ℤ ℚ).injective_int (ha ▸ hg₁m)
  have hcm : c.Monic := monic_of_injective (algebraMap ℤ ℚ).injective_int (hc ▸ hsm)
  have hPeq : P = a * a * c := Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int (by
    rw [Polynomial.map_mul, Polynomial.map_mul, ha, hc, hs])

  have hq0 : aeval t (a * c) = 0 := by
    refine IsReduced.eq_zero _ ⟨2, ?_⟩
    rw [← map_pow, show (a * c) ^ 2 = P * c by rw [hPeq]; ring, map_mul, minpoly.aeval, zero_mul]
  have hmin := minpoly.min ℤ t (ham.mul hcm) hq0
  rw [← hPdef, hPeq, degree_mul, degree_mul, degree_mul] at hmin
  have hapos : 0 < degree a := by
    have : 0 < degree g₁ := degree_pos_of_ne_zero_of_nonunit hg₁m.ne_zero
      (fun hu => hgu (hg₁g.isUnit hu))
    rwa [← ha, degree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at this
  have hafin : degree a ≠ ⊥ := degree_ne_bot.mpr ham.ne_zero
  have hcfin : degree c ≠ ⊥ := degree_ne_bot.mpr hcm.ne_zero
  revert hmin hapos hafin hcfin
  generalize degree a = da; generalize degree c = dc
  cases da with
  | bot => simp
  | coe da =>
    cases dc with
    | bot => simp
    | coe dc =>
      intro hmin hapos _ _
      have h1 : (0 : WithBot ℕ) < da := hapos
      norm_cast at hmin h1
      omega

end Part2

private theorem conj_mem_map_subtype {G : Type} [Group G] {D : Subgroup G} {I : Subgroup ↥D} (hI : I.Normal)
    {σ τ : G} (hσ : σ ∈ D) (hτ : τ ∈ I.map D.subtype) : σ * τ * σ⁻¹ ∈ I.map D.subtype := by
  obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.1 hτ
  exact Subgroup.mem_map.2 ⟨⟨σ, hσ⟩ * τ' * ⟨σ, hσ⟩⁻¹, hI.conj_mem τ' hτ' ⟨σ, hσ⟩, rfl⟩

private theorem exists_frobenius_endo_inertiaCoinvariants {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
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

theorem pi_eq_zero_of_apply_ne_zero_of_mul_eq_zero (N : ℕ) [NeZero N] (S₀ : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (θ' : CuspForm.heckeAlgebra N 2 S₀ →+* ResidueField 𝒪) (r x : CuspForm.heckeAlgebra N 2 S₀)
    (hr : θ' r ≠ 0) (hrx : r * x = 0) : CuspForm.heckeLocal.π N S₀ 𝒪 θ' x = 0 := by
  classical
  have hmem : (1 : 𝒪) ⊗ₜ[ℤ] r ∈ (CuspForm.heckeCharKernel N S₀ 𝒪 θ').primeCompl := by
    rw [Ideal.mem_primeCompl_iff, CuspForm.mem_heckeCharKernel_iff, CuspForm.residualCharacter_tmul, map_one,
      one_mul]
    exact hr
  have hsub : CuspForm.latticeBaseChange N S₀ 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] r) ∈ CuspForm.heckeLocalSubmonoid N S₀ 𝒪 θ' :=
    ⟨(1 : 𝒪) ⊗ₜ[ℤ] r, hmem, rfl⟩
  have hkill : CuspForm.latticeBaseChange N S₀ 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] r) *
      CuspForm.latticeBaseChange N S₀ 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] x) = 0 := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hrx, TensorProduct.tmul_zero, map_zero]
  have hπ : CuspForm.heckeLocal.π N S₀ 𝒪 θ' x =
      algebraMap (CuspForm.heckeBaseAlgebra N S₀ 𝒪) (CuspForm.heckeLocal N S₀ 𝒪 θ')
        (CuspForm.latticeBaseChange N S₀ 𝒪 ((1 : 𝒪) ⊗ₜ[ℤ] x)) := rfl
  rw [hπ, IsLocalization.map_eq_zero_iff (CuspForm.heckeLocalSubmonoid N S₀ 𝒪 θ')]
  exact ⟨⟨_, hsub⟩, hkill⟩

theorem squarefree_X_sq_sub_one : Squarefree (((X ^ 2 - C 1 : ℤ[X])).map (Int.castRingHom ℚ)) := by
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_one]
  exact (Polynomial.separable_X_pow_sub_C (1 : ℚ) (by norm_num) one_ne_zero).squarefree

end RFMain

open RFMain in
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
                LinearMap.trace (ResidueField 𝒪) _ E) :
    IsReduced (CuspForm.heckeLocal N (↑S₀ : Set ℕ) 𝒪 θ') := by
  classical
  have hint : CuspForm.HasIntegralStructure N 2 := Fact.out
  have hpp : p.Prime := Fact.out

  have hpk : (p : ResidueField 𝒪) = 0 := by
    rw [← map_natCast (residue 𝒪), residue_eq_zero_iff]; exact hp𝒪
  haveI : CharP (ResidueField 𝒪) p := by
    obtain ⟨r, hr⟩ := CharP.exists (ResidueField 𝒪)
    have hrp : r ∣ p := (CharP.cast_eq_zero_iff (ResidueField 𝒪) r p).1 hpk
    rcases (Nat.dvd_prime hpp).1 hrp with h1 | h2
    · exact absurd h1 (CharP.char_ne_one (ResidueField 𝒪) r)
    · exact h2 ▸ hr
  have hqunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : 𝒪) := by
    intro q hq hqp
    by_contra hnu
    have hmem : (q : 𝒪) ∈ maximalIdeal 𝒪 := (mem_maximalIdeal _).2 hnu
    have h0 : (q : ResidueField 𝒪) = 0 := by
      rw [← map_natCast (residue 𝒪), residue_eq_zero_iff]; exact hmem
    rw [CharP.cast_eq_zero_iff (ResidueField 𝒪) p q] at h0
    exact hqp ((Nat.prime_dvd_prime_iff_eq hpp hq).1 h0).symm

  let π' := CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ'
  let G : Set (CuspForm.heckeLocal N (↑S₀ : Set ℕ) 𝒪 θ') :=
    {x | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₀ : ℓ ∉ (↑S₀ : Set ℕ)),
        x = π' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀)} ∪
    {x | ∃ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)),
        x = π' (CuspForm.heckeAlgebra.U hq hqN hqS₀)}
  have htop : Algebra.adjoin ℤ ((Subtype.val : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) ⁻¹'
        CuspForm.heckeGenerators N 2 (↑S₀ : Set ℕ)) = ⊤ := by
    apply Subalgebra.map_injective (f := (CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ)).val)
      Subtype.val_injective
    rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val, Subalgebra.coe_val,
      Set.image_preimage_eq_of_subset]
    · rfl
    · rw [Subtype.range_coe]
      exact Algebra.subset_adjoin
  have hadj : Algebra.adjoin 𝒪 G = ⊤ := by
    apply top_le_iff.1
    rw [← CuspForm.heckeLocal.adjoin_range_pi N (↑S₀ : Set ℕ) 𝒪 θ' hint]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    have ht : t ∈ Algebra.adjoin ℤ ((Subtype.val : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) ⁻¹'
          CuspForm.heckeGenerators N 2 (↑S₀ : Set ℕ)) := by
      rw [htop]; exact Algebra.mem_top
    induction ht using Algebra.adjoin_induction with
    | mem t ht =>
      apply Algebra.subset_adjoin
      rcases ht with ⟨ℓ, hℓ, hℓN, hℓS, ht⟩ | ⟨q, hqN, hq, hqS, ht⟩
      · have : t = CuspForm.heckeAlgebra.T hℓ hℓN hℓS := Subtype.ext ht
        exact Or.inl ⟨ℓ, hℓ, hℓN, hℓS, by rw [this]⟩
      · have : t = CuspForm.heckeAlgebra.U hq hqN hqS := Subtype.ext ht
        exact Or.inr ⟨q, hq, hqN, hqS, by rw [this]⟩
    | algebraMap r =>
      rw [eq_intCast, map_intCast]
      exact intCast_mem _ r
    | add x y _ _ ihx ihy =>
      rw [map_add]
      exact Subalgebra.add_mem _ ihx ihy
    | mul x y _ _ ihx ihy =>
      rw [map_mul]
      exact Subalgebra.mul_mem _ ihx ihy

  refine isReduced_of_free_of_adjoin_eq_top G hadj ?_
  rintro x (⟨ℓ, hℓ, hℓN, hℓS₀, rfl⟩ | ⟨q, hq, hqN, hqS₀, rfl⟩)
  ·
    let S₁ : Set ℕ := (↑S₀ : Set ℕ) ∪ {q | q.Prime ∧ q ∣ N}
    have hNS₁ : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S₁ := fun q hq hqN => Or.inr ⟨hq, hqN⟩
    have hS₀S₁ : (↑S₀ : Set ℕ) ⊆ S₁ := Set.subset_union_left
    have hℓS₁ : ℓ ∉ S₁ := by
      rintro (h | ⟨-, h⟩)
      · exact hℓS₀ h
      · exact hℓN h
    haveI := CuspForm.isReduced_heckeAlgebra_of_primeFactors_subset N S₁ hNS₁
    haveI := CuspForm.moduleFinite_heckeAlgebra_two N S₁
    let t₁ : CuspForm.heckeAlgebra N 2 S₁ := CuspForm.heckeAlgebra.T hℓ hℓN hℓS₁
    have ht₁ : IsIntegral ℤ t₁ := Algebra.IsIntegral.isIntegral _
    let incl : CuspForm.heckeAlgebra N 2 S₁ →ₐ[ℤ] CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) :=
      Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hS₀S₁)
    have hincl : incl t₁ = CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀ := Subtype.ext rfl
    refine ⟨minpoly ℤ t₁, squarefree_map_minpoly_of_isReduced t₁ ht₁, ?_⟩
    have h1 : aeval (incl t₁) (minpoly ℤ t₁) = 0 := by
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    have h2 : aeval (π' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀)) (minpoly ℤ t₁) =
        π'.toIntAlgHom (aeval (incl t₁) (minpoly ℤ t₁)) := by
      rw [← hincl]
      exact Polynomial.aeval_algHom_apply π'.toIntAlgHom (incl t₁) _
    rw [h1, map_zero] at h2
    exact h2
  · by_cases hq2 : q ^ 2 ∣ N
    ·
      have hqp : q ≠ p := fun h => hNp (h ▸ hq2)
      have hπ0 := CuspForm.heckeLocal.pi_U_eq_zero_of_sq_dvd_of_not_cube_dvd N (↑S₀ : Set ℕ) 𝒪 θ' q hq hqN hqS₀
        hq2 (hsq q hq hqp hq2).1 (hqunit q hq hqp) (hU0 q hq hqN hqS₀ hq2)
      refine ⟨X, by rw [Polynomial.map_X]; exact Polynomial.irreducible_X.squarefree, ?_⟩
      rw [aeval_X]
      exact hπ0
    · by_cases hqp : q = p
      ·
        subst hqp
        obtain ⟨Pp, σp, Ep, hPp, hσp, hEp⟩ := exists_frobenius_endo_inertiaCoinvariants ρbar q Fact.out
        have hcyc : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic q := by
          refine GaloisRepAdic.detIsCyclotomic_of_forall_frobenius_det_eq (GaloisRepAdic.ofResidualGaloisRep ρbar)
            Fact.out (by rw [hpk]; exact Ideal.zero_mem _) S ?_
          intro ℓ hℓ hℓS B τ hB hτ
          show LinearMap.det (ρbar.ρ τ) = _
          have hℓN' : ¬ ℓ ∣ N := fun h => hℓS (hNS ℓ hℓ h)
          have hℓS₀' : ℓ ∉ (↑S₀ : Set ℕ) := fun h => hℓS (hS₀ (Finset.mem_coe.1 h))
          have hℓp : ℓ ≠ q := fun h => hℓS (h ▸ hpS)
          have hcp := hT ℓ hℓ hℓN' hℓS₀' hℓp B hB τ hτ
          have hdet := LinearMap.det_eq_sign_charpoly_coeff (ρbar.ρ τ)
          rw [hcp, ρbar.finrank_eq] at hdet
          rw [hdet]
          simp [coeff_C, coeff_X]
        have htr : LinearMap.trace (ResidueField 𝒪) _ Ep ≠ 0 :=
          ResidualGaloisRep.trace_inertiaCoinvariants_ne_zero_of_isOrdinaryAt_of_detIsCyclotomic q hp2 ρbar hcyc
            (hord hqN) Pp hPp σp Ep hEp
        have hUp : θ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) ≠ 0 := by
          rw [show CuspForm.heckeAlgebra.U hq hqN hqS₀ = CuspForm.heckeAlgebra.U Fact.out hqN hqS₀ from rfl,
            hU1 q Fact.out hqN hqS₀ hq2 Pp hPp σp hσp Ep hEp]
          exact htr
        obtain ⟨r, P, hr, -, hPsq, hrP⟩ :=
          CuspForm.heckeAlgebra.exists_apply_ne_zero_and_squarefree_and_mul_aeval_U_eq_zero_of_apply_U_ne_zero N (↑S₀ : Set ℕ) θ' q hq hpk hqN hq2 hqS₀ hUp
        refine ⟨P, hPsq, ?_⟩
        have hx : π' (aeval (CuspForm.heckeAlgebra.U hq hqN hqS₀) P) = 0 :=
          pi_eq_zero_of_apply_ne_zero_of_mul_eq_zero N (↑S₀ : Set ℕ) 𝒪 θ' r _ hr hrP
        have h := Polynomial.aeval_algHom_apply π'.toIntAlgHom (CuspForm.heckeAlgebra.U hq hqN hqS₀) P
        exact h.trans hx
      ·
        have hθ'S : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
              ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
                LinearMap.charpoly (ρbar.ρ σ) =
                  X ^ 2 - C (θ' (CuspForm.heckeAlgebra.T hℓ hℓN
                    (fun h => hℓS (Finset.coe_subset.mpr hS₀ h)))) * X + C (ℓ : ResidueField 𝒪) := by
          intro ℓ hℓ hℓN hℓS P hP σ hσ
          have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ Finset.mem_coe.2 hpS)
          exact hT ℓ hℓ hℓN _ hℓp P hP σ hσ
        obtain ⟨r, hr, hrU⟩ :=
          CuspForm.heckeAlgebra.exists_apply_ne_zero_and_mul_U_sq_sub_one_eq_zero_of_not_isUnramifiedAt p hp𝒪 ρbar habs S S₀ hS₀ hS hpS N hNS hNS₀ θ' hθ'S q hq hqp hqN hq2 (hst q hq hqp hqN hq2).1
        refine ⟨X ^ 2 - C 1, squarefree_X_sq_sub_one, ?_⟩
        have hx : π' (CuspForm.heckeAlgebra.U hq hqN (hNS₀ q hq hqN) ^ 2 - 1) = 0 :=
          pi_eq_zero_of_apply_ne_zero_of_mul_eq_zero N (↑S₀ : Set ℕ) 𝒪 θ' r _ hr hrU
        rw [map_sub, map_pow, map_one] at hx
        rw [map_sub, map_pow, aeval_X, aeval_C, map_one]
        exact hx

end S_CuspForm_heckeLocal_isReduced_of_charpoly_frobenius_eq_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_CuspForm_heckeLocal_isReduced_of_charpoly_frobenius_eq_of_isAbsolutelyIrreducible (solution)

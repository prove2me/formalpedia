-- Prove2me | solution 1 for CuspForm.apply_U_eq_intCast_of_point_of_not_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c44b13ab-a2e7-53e0-b78b-a988132cfd4f

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_CuspForm_IsNewform_dvd_level_of_point_of_not_isUnramifiedAt
import Theorems.Thm_CuspForm_heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_exists_isNewform_descent
import Theorems.Thm_CuspForm_qCoeff_sq_eq_one_of_isNewform
import Theorems.Thm_CuspForm_heckeLocal_exists_algHom_of_subset
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_apply_U_eq_intCast_of_point_of_not_isUnramifiedAt
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D"
p2m_attr_erase "simp" "ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing ModularFormClass

namespace N1Main
section Engines

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000
open scoped TensorProduct
open CuspForm

variable (N : ℕ) [NeZero N] (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
variable (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
variable {T : Type} [CommRing T] [Algebra 𝒪 T]

private noncomputable def baseAlgHomOf (hint : HasIntegralStructure N 2)
    (π' : heckeAlgebra N 2 S →+* T) : heckeBaseAlgebra N S 𝒪 →ₐ[𝒪] T :=
  AlgHom.liftEquiv ℤ 𝒪 ↥(heckeLatticeAlgebra N S) T
    (π'.toIntAlgHom.comp
      (AlgEquiv.ofBijective (latticeRestrictHom N S)
        (latticeRestrictHom_bijective N S hint)).symm.toAlgHom)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
private theorem baseAlgHomOf_latticeBaseChange_tmul (hint : HasIntegralStructure N 2)
    (π' : heckeAlgebra N 2 S →+* T) (a : 𝒪) (t : heckeAlgebra N 2 S) :
    baseAlgHomOf N S 𝒪 hint π' (latticeBaseChange N S 𝒪 (a ⊗ₜ t)) =
      algebraMap 𝒪 T a * π' t := by
  rw [latticeBaseChange_tmul]
  show (AlgHom.liftEquiv ℤ 𝒪 ↥(heckeLatticeAlgebra N S) T) _
      (a ⊗ₜ latticeRestrictHom N S t) = _
  rw [AlgHom.liftEquiv_tmul, Algebra.smul_def]
  congr 1
  exact congrArg π' ((AlgEquiv.ofBijective (latticeRestrictHom N S)
    (latticeRestrictHom_bijective N S hint)).symm_apply_apply t)

variable [IsLocalRing T] [IsLocalHom (algebraMap 𝒪 T)]

private theorem residue_baseAlgHomOf_latticeBaseChange (hint : HasIntegralStructure N 2)
    (π' : heckeAlgebra N 2 S →+* T)
    (hπ' : ∀ t, IsLocalRing.residue T (π' t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t))
    (s : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) :
    IsLocalRing.residue T (baseAlgHomOf N S 𝒪 hint π' (latticeBaseChange N S 𝒪 s)) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (residualCharacter N S 𝒪 θ s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a t =>
    rw [baseAlgHomOf_latticeBaseChange_tmul, map_mul, hπ', residualCharacter_tmul,
      map_mul, ← IsLocalRing.ResidueField.map_residue]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem isUnit_baseAlgHomOf_of_mem_submonoid (hint : HasIntegralStructure N 2)
    (π' : heckeAlgebra N 2 S →+* T)
    (hπ' : ∀ t, IsLocalRing.residue T (π' t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t))
    (y : heckeLocalSubmonoid N S 𝒪 θ) :
    IsUnit (baseAlgHomOf N S 𝒪 hint π' y) := by
  obtain ⟨_, s, hs, rfl⟩ := y
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit,
    residue_baseAlgHomOf_latticeBaseChange N S 𝒪 θ hint π' hπ']
  exact fun h0 => hs ((mem_heckeCharKernel_iff N S 𝒪 θ s).mpr
    ((IsLocalRing.ResidueField.map (algebraMap 𝒪 T)).injective (h0.trans (map_zero _).symm)))

private noncomputable def algHomOf (hint : HasIntegralStructure N 2)
    (π' : heckeAlgebra N 2 S →+* T)
    (hπ' : ∀ t, IsLocalRing.residue T (π' t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t)) :
    heckeLocal N S 𝒪 θ →ₐ[𝒪] T :=
  IsLocalization.liftAlgHom (M := heckeLocalSubmonoid N S 𝒪 θ)
    (isUnit_baseAlgHomOf_of_mem_submonoid N S 𝒪 θ hint π' hπ')

private theorem algHomOf_π (hint : HasIntegralStructure N 2)
    (π' : heckeAlgebra N 2 S →+* T)
    (hπ' : ∀ t, IsLocalRing.residue T (π' t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t))
    (t : heckeAlgebra N 2 S) :
    algHomOf N S 𝒪 θ hint π' hπ' (heckeLocal.π N S 𝒪 θ t) = π' t := by
  show IsLocalization.lift _
      (algebraMap (heckeBaseAlgebra N S 𝒪) (heckeLocal N S 𝒪 θ)
        (latticeBaseChange N S 𝒪 ((1 : 𝒪) ⊗ₜ t))) = π' t
  rw [IsLocalization.lift_eq]
  exact (baseAlgHomOf_latticeBaseChange_tmul N S 𝒪 hint π' 1 t).trans
    (by rw [map_one, one_mul])

end Engines

end N1Main

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (N : ℕ) [NeZero N] [Fact (CuspForm.HasIntegralStructure N 2)]
    (S S₀ : Finset ℕ) (hS₀S : S₀ ⊆ S) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hNS₀ : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S₀)
    (θ' : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* ResidueField 𝒪)
    (hθ' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ' (CuspForm.heckeAlgebra.T hℓ hℓN
              (fun h => hℓS (Finset.coe_subset.mpr hS₀S h)))) * X + C (ℓ : ResidueField 𝒪))
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
    [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [IsLocalHom (algebraMap 𝒪 𝒪')]
    (χ : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* 𝒪')
    (hχ : ∀ t, residue 𝒪' (χ t) = ResidueField.map (algebraMap 𝒪 𝒪') (θ' t))
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hqN : q ∣ N) (hq2 : ¬ q ^ 2 ∣ N)
    (hram : ¬ ρbar.IsUnramifiedAt q) :
    ∃ a : ℤ, (a = 1 ∨ a = -1) ∧ χ (CuspForm.heckeAlgebra.U hq hqN (hNS₀ q hq hqN)) = (a : 𝒪') := by
  classical
  have hint : CuspForm.HasIntegralStructure N 2 := Fact.out
  have hqS₀ : q ∉ (↑S₀ : Set ℕ) := hNS₀ q hq hqN

  set 𝔭 : Ideal (CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ)) := RingHom.ker χ with h𝔭def
  have h𝔭 : 𝔭.IsPrime := RingHom.ker_isPrime χ
  obtain ⟨f, hf, hann⟩ := CuspForm.exists_isNormalizedEigenform_annihilator_le_of_isPrime _ 𝔭 h𝔭
  obtain ⟨χf, hχf, hχfT, hχfU⟩ := hf.exists_ringHom_heckeAlgebra (↑S₀ : Set ℕ)
  have hker : ∀ t, χf t = 0 → χ t = 0 := by
    intro t ht
    have h := hχf t
    rw [ht, zero_smul] at h
    exact hann t h
  have hsurj : Function.Surjective χf.rangeRestrict := RingHom.rangeRestrict_surjective χf
  let ι₀ : χf.range →+* 𝒪' :=
    (RingHom.liftOfRightInverse χf.rangeRestrict (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj))
      ⟨χ, fun t ht => by
        rw [RingHom.mem_ker] at ht ⊢
        exact hker t (congrArg Subtype.val ht)⟩
  have hι₀ : ∀ t, ι₀ (χf.rangeRestrict t) = χ t := fun t =>
    RingHom.liftOfRightInverse_comp_apply χf.rangeRestrict _ _ _ t

  obtain ⟨Mg, hMgN, g, hg, hdesc⟩ := CuspForm.exists_isNewform_descent f hf
  haveI : NeZero Mg := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) hMgN⟩
  obtain ⟨chig, -, hchigT, -⟩ := hg.isNormalizedEigenform.exists_ringHom_heckeAlgebra (↑S : Set ℕ)
  have hgenT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS) ∈ χf.range := by
    intro ℓ hℓ hℓMg hℓS
    have hℓN : ¬ ℓ ∣ N := fun h => hℓS (Finset.mem_coe.2 (hNS ℓ hℓ h))
    have hℓS₀ : ℓ ∉ (↑S₀ : Set ℕ) := fun h => hℓS (Finset.coe_subset.mpr hS₀S h)
    refine RingHom.mem_range.2 ⟨CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀, ?_⟩
    rw [hχfT ℓ hℓ hℓN hℓS₀, hchigT ℓ hℓ hℓMg hℓS, hdesc ℓ hℓ hℓN]
  have hgenU : ∀ (q' : ℕ) (hq' : q'.Prime) (hq'Mg : q' ∣ Mg) (hq'S : q' ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.U hq' hq'Mg hq'S) ∈ χf.range :=
    fun q' hq' hq'Mg hq'S => absurd (Finset.mem_coe.2 (hNS q' hq' (hq'Mg.trans hMgN))) hq'S
  have htop : Algebra.adjoin ℤ ((Subtype.val : CuspForm.heckeAlgebra Mg 2 (↑S : Set ℕ) →
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 Mg) 2)) ⁻¹'
        CuspForm.heckeGenerators Mg 2 (↑S : Set ℕ)) = ⊤ := by
    apply Subalgebra.map_injective (f := (CuspForm.heckeAlgebra Mg 2 (↑S : Set ℕ)).val)
      Subtype.val_injective
    rw [← Algebra.adjoin_image, Algebra.map_top, Subalgebra.range_val, Subalgebra.coe_val,
      Set.image_preimage_eq_of_subset]
    · rfl
    · rw [Subtype.range_coe]
      exact Algebra.subset_adjoin
  have hmem' : ∀ t : CuspForm.heckeAlgebra Mg 2 (↑S : Set ℕ), chig t ∈ χf.range := by
    intro t
    have ht : t ∈ Algebra.adjoin ℤ ((Subtype.val : CuspForm.heckeAlgebra Mg 2 (↑S : Set ℕ) →
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 Mg) 2)) ⁻¹'
          CuspForm.heckeGenerators Mg 2 (↑S : Set ℕ)) := by
      rw [htop]; exact Algebra.mem_top
    induction ht using Algebra.adjoin_induction with
    | mem t ht =>
      rcases ht with ⟨ℓ, hℓ, hℓMg, hℓS, ht⟩ | ⟨q', hq'Mg, hq', hq'S, ht⟩
      · have : t = CuspForm.heckeAlgebra.T hℓ hℓMg hℓS := Subtype.ext ht
        rw [this]; exact hgenT ℓ hℓ hℓMg hℓS
      · have : t = CuspForm.heckeAlgebra.U hq' hq'Mg hq'S := Subtype.ext ht
        rw [this]; exact hgenU q' hq' hq'Mg hq'S
    | algebraMap r =>
      rw [eq_intCast, map_intCast chig]
      exact intCast_mem _ r
    | add x y _ _ ihx ihy =>
      rw [chig.map_add]
      exact add_mem ihx ihy
    | mul x y _ _ ihx ihy =>
      rw [chig.map_mul]
      exact mul_mem ihx ihy

  let Θ : CuspForm.heckeAlgebra Mg 2 (↑S : Set ℕ) →+* 𝒪' := ι₀.comp (chig.codRestrict χf.range hmem')
  have hΘ : ∀ t, Θ t = ι₀ ⟨chig t, hmem' t⟩ := fun t => rfl
  have hsurjg : Function.Surjective chig.rangeRestrict := RingHom.rangeRestrict_surjective chig
  let ι : chig.range →+* 𝒪' :=
    (RingHom.liftOfRightInverse chig.rangeRestrict (Function.surjInv hsurjg)
      (Function.rightInverse_surjInv hsurjg))
      ⟨Θ, fun t ht => by
        rw [RingHom.mem_ker] at ht ⊢
        have h0 : chig t = 0 := congrArg Subtype.val ht
        rw [hΘ]
        have : (⟨chig t, hmem' t⟩ : χf.range) = 0 := Subtype.ext h0
        rw [this, map_zero]⟩
  have hι : ∀ t, ι (chig.rangeRestrict t) = ι₀ ⟨chig t, hmem' t⟩ := fun t =>
    RingHom.liftOfRightInverse_comp_apply chig.rangeRestrict _ _ _ t

  let incl : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →ₐ[ℤ] CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) :=
    Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀S))
  let θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪 := θ'.comp incl.toRingHom
  have hθincl : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), θ t = θ' (incl t) := fun t => rfl
  have hTincl : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      incl (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) =
        CuspForm.heckeAlgebra.T hℓ hℓN (fun h => hℓS (Finset.coe_subset.mpr hS₀S h)) := by
    intro ℓ hℓ hℓN hℓS
    exact Subtype.ext rfl
  have hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪) := by
    intro ℓ hℓ hℓN hℓS P hP σ hσ
    rw [hθincl, hTincl]
    exact hθ' ℓ hℓ hℓN hℓS P hP σ hσ
  obtain ⟨Ψ, -, hΨ⟩ :=
    CuspForm.heckeLocal.exists_algHom_of_subset N (↑S : Set ℕ) (↑S₀ : Set ℕ)
      (Finset.coe_subset.mpr hS₀S) 𝒪 θ' θ hθincl
  let ψ' : CuspForm.heckeLocal N (↑S₀ : Set ℕ) 𝒪 θ' →ₐ[𝒪] 𝒪' := N1Main.algHomOf N (↑S₀ : Set ℕ) 𝒪 θ' hint χ hχ
  have hψ' : ∀ t, ψ' (CuspForm.heckeLocal.π N (↑S₀ : Set ℕ) 𝒪 θ' t) = χ t :=
    N1Main.algHomOf_π N (↑S₀ : Set ℕ) 𝒪 θ' hint χ hχ
  let ψ₀ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] 𝒪' := ψ'.comp Ψ
  have hiota : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ι (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN)) hℓS)) =
        ψ₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := by
    intro ℓ hℓ hℓN hℓS
    have hℓS₀ : ℓ ∉ (↑S₀ : Set ℕ) := fun h => hℓS (Finset.coe_subset.mpr hS₀S h)
    rw [hι]
    show ι₀ ⟨chig _, _⟩ = ψ' (Ψ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ _))
    rw [hΨ, hψ']
    have h1 : (⟨chig (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN)) hℓS), hmem' _⟩ : χf.range) =
        χf.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀) := by
      apply Subtype.ext
      show chig (CuspForm.heckeAlgebra.T hℓ (fun h => hℓN (h.trans hMgN)) hℓS) =
        χf (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀)
      rw [hχfT ℓ hℓ hℓN hℓS₀, hchigT ℓ hℓ _ hℓS, hdesc ℓ hℓ hℓN]
    rw [h1, hι₀]
    show χ _ = χ (incl _)
    rw [hTincl]

  have hqMg : q ∣ Mg :=
    CuspForm.IsNewform.dvd_level_of_point_of_not_isUnramifiedAt p hp𝒪 ρbar habs S hS hpS N hNS θ hθ 𝒪' ψ₀
      Mg hMgN g hg chig hchigT ι hiota q hq hqp hram
  have hq2Mg : ¬ q ^ 2 ∣ Mg := fun h => hq2 (h.trans hMgN)
  have hqNM : ¬ q ∣ N / Mg := by
    intro h
    apply hq2
    have h2 : q * q ∣ Mg * (N / Mg) := mul_dvd_mul hqMg h
    rwa [Nat.mul_div_cancel' hMgN, ← pow_two] at h2

  have hfT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
      CuspForm.heckeTLin 2 hℓ hℓN f = qCoeff g ℓ • f := by
    intro ℓ hℓ hℓN hℓS₀
    have hℓS₀' : ℓ ∉ (↑S₀ : Set ℕ) := fun h => hℓS₀ (Finset.mem_coe.1 h)
    have h := hχf (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀')
    rw [CuspForm.heckeAlgebra.coe_T, hχfT ℓ hℓ hℓN hℓS₀', ← hdesc ℓ hℓ hℓN] at h
    exact h
  have hUf : CuspForm.heckeULin 2 (hqMg.trans hMgN) f = qCoeff g q • f :=
    CuspForm.heckeULin_eq_qCoeff_smul_of_isNewform_of_dvd_of_not_dvd_div N Mg hMgN S₀ g hg q hq hqMg hqNM f hfT
  have hsq : qCoeff g q ^ 2 = 1 := CuspForm.qCoeff_sq_eq_one_of_isNewform hg q hq hqMg hq2Mg
  obtain ⟨a, ha, haq⟩ : ∃ a : ℤ, (a = 1 ∨ a = -1) ∧ qCoeff g q = (a : ℂ) := by
    have h1 : qCoeff g q * qCoeff g q = 1 := by rw [← pow_two]; exact hsq
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, Int.cast_one]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, Int.cast_neg, Int.cast_one]⟩
  refine ⟨a, ha, ?_⟩

  have e1 : ((CuspForm.heckeAlgebra.U hq hqN hqS₀ : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ)) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = (a : ℂ) • f := by
    rw [CuspForm.heckeAlgebra.coe_U, ← haq]
    exact hUf
  have e2 : (((a : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ)) : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ)) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = (a : ℂ) • f := by
    rw [SubringClass.coe_intCast, Module.End.intCast_apply, Int.cast_smul_eq_zsmul]
  have hmem : CuspForm.heckeAlgebra.U hq hqN hqS₀ - (a : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ)) ∈ 𝔭 := by
    apply hann
    rw [AddSubgroupClass.coe_sub, LinearMap.sub_apply, e1, e2, sub_self]
  have hχ0 : χ (CuspForm.heckeAlgebra.U hq hqN hqS₀ - (a : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ))) = 0 :=
    (RingHom.mem_ker).1 hmem
  rw [map_sub, map_intCast, sub_eq_zero] at hχ0
  exact hχ0

end S_CuspForm_apply_U_eq_intCast_of_point_of_not_isUnramifiedAt
end P2MW
export P2MW.S_CuspForm_apply_U_eq_intCast_of_point_of_not_isUnramifiedAt (solution)

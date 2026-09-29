-- Prove2me | solution 1 for GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d9204423-c30f-5eec-9c40-c27b4edbfc5d

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom
import Theorems.Thm_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
import Theorems.Thm_CohCarrier_exists_ringHom_heckeAlgebra_apply_smul_eq_heckeT_of_mem_parabolicHoms
import Theorems.Thm_CohCarrier_exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int
import Theorems.Thm_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero
import Theorems.Thm_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder
import Theorems.Thm_GaloisRep_exists_galoisRep_trace_eq_of_ringHom_heckeAlgebra_two
import Theorems.Thm_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule TateModule.instModule TateModule.instSMul ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.injEq TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply"
p2m_attr_erase "simp" "AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

namespace WeightTwoModPAssembly

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Bridge

variable (N : ℕ) (κ : Type*) [CommRing κ]

noncomputable abbrev triv : Representation κ (Gamma0 N) κ := 1

theorem coeffCoboundaries_triv_eq_bot : coeffCoboundaries (triv N κ) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun z hz => ?_
  obtain ⟨v, rfl⟩ := (mem_coeffCoboundaries_iff _ _).mp hz
  funext g
  simp [triv]

theorem mem_coeffCocycles_triv_iff (z : Gamma0 N → κ) :
    z ∈ coeffCocycles (triv N κ) ↔ ∀ g h : Gamma0 N, z (g * h) = z g + z h := by
  rw [mem_coeffCocycles_iff]
  simp [triv]

variable {N κ}

def homOfCocycle (z : ↥(coeffCocycles (triv N κ))) : Additive (Gamma0 N) →+ κ where
  toFun g := (z : Gamma0 N → κ) (Additive.toMul g)
  map_zero' := by
    have h := (mem_coeffCocycles_triv_iff N κ z).mp z.2 1 1
    rw [mul_one] at h
    have h' : (z : Gamma0 N → κ) 1 + (z : Gamma0 N → κ) 1 = (z : Gamma0 N → κ) 1 + 0 := by
      rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  map_add' g h := (mem_coeffCocycles_triv_iff N κ z).mp z.2 (Additive.toMul g) (Additive.toMul h)

@[scoped simp] theorem homOfCocycle_apply (z : ↥(coeffCocycles (triv N κ))) (g : Gamma0 N) :
    homOfCocycle z (Additive.ofMul g) = (z : Gamma0 N → κ) g := rfl

def cocycleOfHom (f : Additive (Gamma0 N) →+ κ) : ↥(coeffCocycles (triv N κ)) :=
  ⟨fun g => f (Additive.ofMul g), (mem_coeffCocycles_triv_iff N κ _).mpr fun g h => by
    rw [ofMul_mul, map_add]⟩

variable (N κ)

def cocycleEquiv : ↥(coeffCocycles (triv N κ)) ≃ₗ[κ] (Additive (Gamma0 N) →+ κ) where
  toFun := homOfCocycle
  invFun := cocycleOfHom
  map_add' _ _ := AddMonoidHom.ext fun _ => rfl
  map_smul' _ _ := AddMonoidHom.ext fun _ => rfl
  left_inv _ := Subtype.ext (funext fun _ => rfl)
  right_inv _ := AddMonoidHom.ext fun _ => rfl

noncomputable def H1equiv : coeffH1 (triv N κ) ≃ₗ[κ] (Additive (Gamma0 N) →+ κ) :=
  (Submodule.quotEquivOfEqBot _ (by
      rw [coeffCoboundaries_triv_eq_bot, Submodule.comap_bot, Submodule.ker_subtype])).trans
    (cocycleEquiv N κ)

theorem H1equiv_mk (z : ↥(coeffCocycles (triv N κ))) :
    H1equiv N κ (coeffH1Mk _ z) = homOfCocycle z := rfl

theorem H1equiv_apply_of_isCoeffHeckeOnH1 (ℓ : ℕ) [NeZero ℓ]
    {T : coeffH1 (triv N κ) →ₗ[κ] coeffH1 (triv N κ)} (hT : IsCoeffHeckeOnH1 N ℓ (triv N κ) LinearMap.id T)
    (x : coeffH1 (triv N κ)) :
    H1equiv N κ (T x) = heckeOperatorHom N ℓ κ (H1equiv N κ x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  obtain ⟨w, hw, hTw⟩ := hT z
  rw [hTw, H1equiv_mk, H1equiv_mk]
  refine AddMonoidHom.ext fun g => ?_
  have key : homOfCocycle w (Additive.ofMul (Additive.toMul g)) =
      heckeOperatorHom N ℓ κ (homOfCocycle z) (Additive.ofMul (Additive.toMul g)) := by
    rw [homOfCocycle_apply, hw]
    exact coeffHeckeFun_trivial N ℓ (homOfCocycle z) (Additive.toMul g)
  simpa using key

theorem exists_hom_of_isEigensystemH1_one (S₀ : Set ℕ) (lam : ℕ → κ)
    (h : IsEigensystemH1 N (1 : Representation κ (Gamma0 N) κ) (fun _ => LinearMap.id) S₀ lam) :
    ∃ f : Additive (Gamma0 N) →+ κ, f ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHom N ℓ κ f = lam ℓ • f) := by
  obtain ⟨x, hx, hT⟩ := h
  refine ⟨H1equiv N κ x, fun h => hx ((H1equiv N κ).map_eq_zero_iff.mp h), fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT, hTx⟩ := hT ℓ hℓ hℓN hℓS
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [← H1equiv_apply_of_isCoeffHeckeOnH1 N κ ℓ hT, hTx, map_smul]

end Bridge

section Carrier

variable (N : ℕ)

def inclTop : ↥(CohCarrier.GammaH N ⊤) →* Gamma0 N where
  toFun γ := ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {N} {A : Type*} [AddCommGroup A]

def toCarrier (f : Additive (Gamma0 N) →+ A) : CohCarrier.H1 N ⊤ A :=
  f.comp (MonoidHom.toAdditive (inclTop N))

theorem toCarrier_apply (f : Additive (Gamma0 N) →+ A) (γ : ↥(CohCarrier.GammaH N ⊤)) :
    toCarrier f (Additive.ofMul γ) =
      f (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) := rfl

theorem toCarrier_ne_zero {f : Additive (Gamma0 N) →+ A} (hf : f ≠ 0) : toCarrier f ≠ 0 := by
  intro h
  apply hf
  refine AddMonoidHom.ext fun g => ?_
  have hg : ((Additive.toMul g : Gamma0 N) : SL(2, ℤ)) ∈ CohCarrier.GammaH N ⊤ := by
    rw [CohCarrier.GammaH_top]; exact (Additive.toMul g).2
  have := congrArg (fun F : CohCarrier.H1 N ⊤ A => F (Additive.ofMul ⟨_, hg⟩)) h
  simpa [toCarrier_apply] using this

theorem heckeT_toCarrier (ℓ : ℕ) [NeZero ℓ] (f : Additive (Gamma0 N) →+ A) :
    CohCarrier.heckeT N ⊤ ℓ A (toCarrier f) = toCarrier (heckeOperatorHom N ℓ A f) := by
  refine AddMonoidHom.ext fun g => ?_
  have h := CohCarrier.heckeT_top_apply_eq_heckeOperatorHom N ℓ A (toCarrier f) f
    (fun γ => rfl) (Additive.toMul g)
  simp [toCarrier_apply] at h
  exact h

end Carrier

section Algebra

theorem smul_cancel {M : ℕ} {H : Subgroup (ZMod M)ˣ} {K : Type*} [Field K] {F : CohCarrier.H1 M H K}
    (hF : F ≠ 0) {a b : K} (h : a • F = b • F) : a = b := by
  by_contra hab
  apply hF
  refine AddMonoidHom.ext fun m => ?_
  have hm := congrArg (fun G : CohCarrier.H1 M H K => G m) h
  simp only [AddMonoidHom.smul_apply, smul_eq_mul] at hm
  have : (a - b) * F m = 0 := by rw [sub_mul, hm, sub_self]
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hab
  · simpa using h1

theorem isIntegral_of_pow_eq_one {z : ℂ} {m : ℕ} (hm : 0 < m) (hz : z ^ m = 1) : IsIntegral ℤ z :=
  IsIntegral.of_pow hm (by rw [hz]; exact isIntegral_one)

theorem isIntegral_unitsHom_apply {G : Type*} [Group G] [Finite G] (e : G →* ℂˣ) (g : G) :
    IsIntegral ℤ ((e g : ℂˣ) : ℂ) := by
  have hg : IsOfFinOrder g := isOfFinOrder_of_finite g
  obtain ⟨m, hm, hgm⟩ := hg.exists_pow_eq_one
  refine isIntegral_of_pow_eq_one hm ?_
  rw [← Units.val_pow_eq_pow_val, ← map_pow, hgm, map_one, Units.val_one]

noncomputable def reduceUnitsHom {G : Type*} [Group G] [Finite G] {κ : Type*} [CommRing κ]
    (φ' : integralClosure ℤ ℂ →+* κ) (e : G →* ℂˣ) : G →* κˣ where
  toFun g :=
    ⟨φ' ⟨(e g : ℂ), isIntegral_unitsHom_apply e g⟩, φ' ⟨(e g⁻¹ : ℂ), isIntegral_unitsHom_apply e g⁻¹⟩,
      by
        rw [← map_mul, ← map_one φ']
        congr 1
        apply Subtype.ext
        change ((e g : ℂˣ) : ℂ) * ((e g⁻¹ : ℂˣ) : ℂ) = 1
        rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one],
      by
        rw [← map_mul, ← map_one φ']
        congr 1
        apply Subtype.ext
        change ((e g⁻¹ : ℂˣ) : ℂ) * ((e g : ℂˣ) : ℂ) = 1
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]⟩
  map_one' := by
    apply Units.ext
    change φ' ⟨((e 1 : ℂˣ) : ℂ), _⟩ = 1
    rw [← map_one φ']
    congr 1
    apply Subtype.ext
    change ((e 1 : ℂˣ) : ℂ) = 1
    rw [map_one, Units.val_one]
  map_mul' g h := by
    apply Units.ext
    change φ' ⟨((e (g * h) : ℂˣ) : ℂ), _⟩ = φ' ⟨((e g : ℂˣ) : ℂ), _⟩ * φ' ⟨((e h : ℂˣ) : ℂ), _⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    change ((e (g * h) : ℂˣ) : ℂ) = ((e g : ℂˣ) : ℂ) * ((e h : ℂˣ) : ℂ)
    rw [map_mul, Units.val_mul]

theorem coe_reduceUnitsHom_apply {G : Type*} [Group G] [Finite G] {κ : Type*} [CommRing κ]
    (φ' : integralClosure ℤ ℂ →+* κ) (e : G →* ℂˣ) (g : G) :
    ((reduceUnitsHom φ' e g : κˣ) : κ) = φ' ⟨(e g : ℂ), isIntegral_unitsHom_apply e g⟩ := rfl

end Algebra

section Diamond

variable (N : ℕ) [NeZero N]

theorem diamondL_top_apply (𝒪 : Type) [CommRing 𝒪] (u : (ZMod N)ˣ) (X : CohCarrier.H1 N ⊤ 𝒪) :
    CohCarrier.diamondL N ⊤ 𝒪 u X = X := by
  obtain ⟨σ, hσ⟩ := CohCarrier.gamma0Units_surjective N u
  rw [CohCarrier.diamondL_eq_diamondRaw N ⊤ 𝒪 u σ hσ]
  refine AddMonoidHom.ext fun g => ?_
  change X (Additive.ofMul (CohCarrier.conjHom N ⊤ σ (Additive.toMul g))) = X g
  have hσ' : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH N ⊤ := by
    rw [CohCarrier.GammaH_top]; exact σ.2
  set τ : ↥(CohCarrier.GammaH N ⊤) := ⟨(σ : SL(2, ℤ)), hσ'⟩ with hτ
  have hconj : CohCarrier.conjHom N ⊤ σ (Additive.toMul g) = τ * Additive.toMul g * τ⁻¹ :=
    Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, ofMul_toMul]
  abel

end Diamond

end WeightTwoModPAssembly
p2m_reactivate "P2MW.S_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom.WeightTwoModPAssembly"

open WeightTwoModPAssembly CongruenceSubgroup HeckeEis in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N (1 : Representation κ (CongruenceSubgroup.Gamma0 N) κ)
      (fun _ => LinearMap.id) S₀ lam) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val = lam ℓ) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : κ)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by
  classical

  obtain ⟨f, hf0, hfT⟩ := exists_hom_of_isEigensystemH1_one N κ S₀ lam hocc
  set x : CohCarrier.H1 N ⊤ κ := toCarrier f with hxdef
  have hx0 : x ≠ 0 := toCarrier_ne_zero hf0
  have hxT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N ⊤ ℓ κ x) = lam ℓ • x := by
    intro ℓ hℓ hℓN hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    change CohCarrier.heckeT N ⊤ ℓ κ (toCarrier f) = lam ℓ • toCarrier f
    rw [heckeT_toCarrier, hfT ℓ hℓ hℓN hℓS]
    rfl

  set W : Submodule κ (CohCarrier.H1 N ⊤ κ) :=
    Submodule.span κ (Set.range fun G : CohCarrier.H1 N ⊤ ℤ => (Int.castAddHom κ).comp G) with hWdef
  by_cases hxW : x ∈ W
  swap
  ·

    have hγ : ∃ γ : ↥(CohCarrier.GammaH N ⊤), IsOfFinOrder γ ∧ x (Additive.ofMul γ) ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hxW (CohCarrier.mem_span_int_of_forall_isOfFinOrder_apply_eq_zero N ⊤ κ x hne)
    obtain ⟨γ, hγfin, hγx⟩ := hγ
    have hlam : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = (ℓ : κ) + 1 := by
      intro ℓ hℓ hℓN hℓS
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have h1 := CohCarrier.heckeT_top_apply_eq_smul_of_isOfFinOrder N κ ℓ hℓ hℓN x γ hγfin
      have h2 := congrArg (fun F : CohCarrier.H1 N ⊤ κ => F (Additive.ofMul γ)) (hxT ℓ hℓ hℓN hℓS)
      simp only [AddMonoidHom.smul_apply, smul_eq_mul] at h2
      change CohCarrier.heckeT N ⊤ ℓ κ x (Additive.ofMul γ) = (ℓ + 1) • x (Additive.ofMul γ) at h1
      rw [h1, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h2
      exact (mul_right_cancel₀ hγx h2).symm
    obtain ⟨ρ, hfin, htrdet, hin⟩ :=
      GaloisRep.exists_galoisRep_trace_eq_add_mul_of_unitsHom p N κ 1 1
    refine ⟨ρ, hfin, ?_, ?_, hin⟩
    · intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
      rw [(htrdet ℓ hℓ hℓN hℓp A hA σ hσ).1, hlam ℓ hℓ hℓN hℓS]
      simp only [MonoidHom.one_apply, Units.val_one]
      ring
    · intro ℓ hℓ hℓN hℓp A hA σ hσ
      rw [(htrdet ℓ hℓ hℓN hℓp A hA σ hσ).2]
      simp only [MonoidHom.one_apply, Units.val_one]
      ring
  ·
    obtain ⟨X, θ, φ', hX0, hXT, hθ⟩ :=
      CohCarrier.exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int p N ⊤ S₀ κ φ lam x hx0 hxW hxT
    by_cases hXpar : X ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ
    ·
      set S' : Set ℕ := {n | n ∈ S₀ ∨ n ∣ N} with hS'def
      have hMS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S' := fun q _ hq => Or.inr hq
      have hS'S : ∀ ℓ : ℕ, ¬ ℓ ∣ N → (ℓ ∉ S' ↔ ℓ ∉ S₀) := fun ℓ hℓN =>
        ⟨fun h hS => h (Or.inl hS), fun h hS' => hS'.elim h hℓN⟩
      have heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S' →
          ∃ a : ℂ, (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N ⊤ ℓ ℂ X) = a • X :=
        fun ℓ hℓ hℓN hℓS' => ⟨_, hXT ℓ hℓ hℓN ((hS'S ℓ hℓN).mp hℓS')⟩
      obtain ⟨χℂ, hχℂ⟩ :=
        CohCarrier.exists_ringHom_heckeAlgebra_apply_smul_eq_heckeT_of_mem_parabolicHoms N S' hMS ℂ X
          hXpar hX0 heig

      have hχθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS' : ℓ ∉ S'),
          χℂ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS') = ((θ ℓ : integralClosure ℤ ℂ) : ℂ) := by
        intro ℓ hℓ hℓN hℓS'
        have h1 := hχℂ ℓ hℓ hℓN hℓS'
        have h2 := hXT ℓ hℓ hℓN ((hS'S ℓ hℓN).mp hℓS')
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        change CohCarrier.heckeT N ⊤ ℓ ℂ X = _ at h1
        change CohCarrier.heckeT N ⊤ ℓ ℂ X = _ at h2
        rw [h1] at h2
        exact smul_cancel hX0 h2

      have hint : ∀ t : CuspForm.heckeAlgebra N 2 S', IsIntegral ℤ (χℂ t) := by
        rintro ⟨v, hv⟩
        induction hv using Algebra.adjoin_induction with
        | mem v hv =>
          rcases hv with ⟨ℓ, hℓ, hℓN, hℓS', rfl⟩ | ⟨q, hqN, hq, hqS', rfl⟩
          · have : (⟨CuspForm.heckeTLin 2 hℓ hℓN, Algebra.subset_adjoin
                (CuspForm.heckeTLin_mem_heckeGenerators hℓ hℓN hℓS')⟩ : CuspForm.heckeAlgebra N 2 S') =
                CuspForm.heckeAlgebra.T hℓ hℓN hℓS' := rfl
            rw [this, hχθ ℓ hℓ hℓN hℓS']
            exact (θ ℓ).2
          · exact absurd (hMS q hq hqN) hqS'
        | algebraMap r =>
          have : (⟨algebraMap ℤ _ r, Subalgebra.algebraMap_mem _ r⟩ : CuspForm.heckeAlgebra N 2 S') =
              algebraMap ℤ (CuspForm.heckeAlgebra N 2 S') r := rfl
          rw [this, eq_intCast, map_intCast χℂ r]
          have hr := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := r)
          rwa [eq_intCast] at hr
        | add v w hv hw ihv ihw =>
          have : (⟨v + w, add_mem hv hw⟩ : CuspForm.heckeAlgebra N 2 S') = ⟨v, hv⟩ + ⟨w, hw⟩ := rfl
          rw [this, χℂ.map_add]
          exact ihv.add ihw
        | mul v w hv hw ihv ihw =>
          have : (⟨v * w, mul_mem hv hw⟩ : CuspForm.heckeAlgebra N 2 S') = ⟨v, hv⟩ * ⟨w, hw⟩ := rfl
          rw [this, χℂ.map_mul]
          exact ihv.mul ihw
      set χint : CuspForm.heckeAlgebra N 2 S' →+* integralClosure ℤ ℂ :=
        χℂ.codRestrict (integralClosure ℤ ℂ) hint with hχint
      set χκ : CuspForm.heckeAlgebra N 2 S' →+* κ := φ'.comp χint with hχκ
      have hχκT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS' : ℓ ∉ S'),
          χκ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS') = lam ℓ := by
        intro ℓ hℓ hℓN hℓS'
        rw [← hθ ℓ hℓ hℓN ((hS'S ℓ hℓN).mp hℓS'), hχκ, RingHom.comp_apply]
        congr 1
        apply Subtype.ext
        rw [hχint, RingHom.codRestrict_apply]
        exact hχθ ℓ hℓ hℓN hℓS'
      obtain ⟨ρ, hfin, htr, hdet, hin⟩ :=
        GaloisRep.exists_galoisRep_trace_eq_of_ringHom_heckeAlgebra_two p N S' κ φ χκ
      refine ⟨ρ, hfin, ?_, hdet, hin⟩
      intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
      rw [htr ℓ hℓ hℓN ((hS'S ℓ hℓN).mpr hℓS) hℓp A hA σ hσ, hχκT]
    ·
      have hD : ∀ u : (ZMod N)ˣ, CohCarrier.diamondL N ⊤ ℂ u X = ((1 : (ZMod N)ˣ →* ℂˣ) u : ℂ) • X := by
        intro u
        rw [diamondL_top_apply, MonoidHom.one_apply, Units.val_one, one_smul]
      obtain ⟨ψ₁, ψ₂, hprod, hsum⟩ :=
        CohCarrier.exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul N ⊤ S₀ X hXpar
          (fun ℓ => ((θ ℓ : integralClosure ℤ ℂ) : ℂ)) 1
          (fun ℓ hℓ hℓS hℓN => hXT ℓ hℓ hℓN hℓS) hD

      set ψ₁' : (ZMod N)ˣ →* κˣ := reduceUnitsHom φ' ψ₁.toUnitHom with hψ₁'
      set ψ₂' : (ZMod N)ˣ →* κˣ := reduceUnitsHom φ' ψ₂.toUnitHom with hψ₂'
      have hprod' : ∀ u : (ZMod N)ˣ, ((ψ₁' u : κˣ) : κ) * ((ψ₂' u : κˣ) : κ) = 1 := by
        intro u
        rw [hψ₁', hψ₂', coe_reduceUnitsHom_apply, coe_reduceUnitsHom_apply, ← map_mul, ← map_one φ']
        congr 1
        apply Subtype.ext
        change ((ψ₁.toUnitHom u : ℂˣ) : ℂ) * ((ψ₂.toUnitHom u : ℂˣ) : ℂ) = 1
        rw [MulChar.coe_toUnitHom, MulChar.coe_toUnitHom, hprod u, MonoidHom.one_apply, Units.val_one]
      have hsum' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S₀ →
          lam ℓ = ((ψ₁' (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κˣ) : κ) +
            (ℓ : κ) * ((ψ₂' (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κˣ) : κ) := by
        intro ℓ hℓ hℓN hℓS
        rw [← hθ ℓ hℓ hℓN hℓS, hψ₁', hψ₂', coe_reduceUnitsHom_apply, coe_reduceUnitsHom_apply]
        have key : θ ℓ =
            ⟨(ψ₁.toUnitHom (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : ℂ),
                isIntegral_unitsHom_apply _ _⟩ +
              (ℓ : integralClosure ℤ ℂ) *
                ⟨(ψ₂.toUnitHom (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : ℂ),
                  isIntegral_unitsHom_apply _ _⟩ := by
          apply Subtype.ext
          rw [hsum ℓ hℓ hℓS hℓN]
          simp only [Subalgebra.coe_add, Subalgebra.coe_mul, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]
          norm_cast
        rw [key, map_add, map_mul, map_natCast]
      obtain ⟨ρ, hfin, htrdet, hin⟩ :=
        GaloisRep.exists_galoisRep_trace_eq_add_mul_of_unitsHom p N κ ψ₁' ψ₂'
      refine ⟨ρ, hfin, ?_, ?_, hin⟩
      · intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
        rw [(htrdet ℓ hℓ hℓN hℓp A hA σ hσ).1, hsum' ℓ hℓ hℓN hℓS]
      · intro ℓ hℓ hℓN hℓp A hA σ hσ
        rw [(htrdet ℓ hℓ hℓN hℓp A hA σ hσ).2, hprod', one_mul]

end S_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom
end P2MW
export P2MW.S_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom (solution)

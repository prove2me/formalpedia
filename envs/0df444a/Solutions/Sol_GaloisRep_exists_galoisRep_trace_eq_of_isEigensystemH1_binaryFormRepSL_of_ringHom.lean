-- Prove2me | solution 1 for GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b955b291-0fad-5f06-a502-aca9262ecc67

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_HeckeEis_exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom
import Theorems.Thm_HeckeEis_exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
import Theorems.Thm_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom
import Theorems.Thm_ValuationSubring_smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
import Theorems.Thm_ExtCitation_cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CohCarrier.GammaHLower_finiteIndex ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule TateModule.instModule TateModule.instSMul ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "instance" "WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "HeckeEis.gamma0NebenRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero"
p2m_attr_erase "simp" "TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left"
p2m_attr_erase "simp" "AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

namespace DeligneModPAssembly

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Cyclo

variable (p : ℕ) [Fact p.Prime]

theorem cycloChar_spec (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ)
    (hμ : μ ^ p = 1) :
    σ μ = μ ^ ((ExtCitation.cycloChar p σ : (ZMod p)ˣ) : ZMod p).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne p)] at hμ
    exact zero_ne_one hμ
  have ht : Units.mk0 μ hμ0 ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ, Units.val_one]
  exact modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (ExtCitation.card_rootsOfUnity_eq_self p)
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) ht

theorem exists_isPrimitiveRoot : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p :=
  HasEnoughRootsOfUnity.prim

variable (κ : Type) [Field κ] [CharP κ p]

noncomputable def cycloK : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* κˣ :=
  (Units.map ((ZMod.castHom (dvd_refl p) κ).toMonoidHom)).comp (ExtCitation.cycloChar p)

theorem coe_cycloK_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloK p κ σ : κˣ) : κ) =
      ZMod.castHom (dvd_refl p) κ ((ExtCitation.cycloChar p σ : (ZMod p)ˣ) : ZMod p) :=
  rfl

theorem cycloK_eq_one_of_cycloChar_eq_one {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (h : ExtCitation.cycloChar p σ = 1) : cycloK p κ σ = 1 := by
  rw [cycloK, MonoidHom.comp_apply, h, map_one]

theorem galoisFactorsThroughFiniteLevel_cycloK : GaloisFactorsThroughFiniteLevel (cycloK p κ) := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p
  refine ⟨IntermediateField.adjoin ℚ {ζ}, ?_, ?_⟩
  · exact IntermediateField.adjoin.finiteDimensional
      ((hζ.isIntegral (Fact.out : p.Prime).pos).tower_top)
  · intro σ hσ
    have hfix : σ ζ = ζ := hσ ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ)
    exact cycloK_eq_one_of_cycloChar_eq_one p κ
      (ExtCitation.cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p σ hζ hfix)

theorem coe_cycloK_of_isFrobeniusAt (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    ((cycloK p κ σ : κˣ) : κ) = (ℓ : κ) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p
  have hℓp' : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)
  have h1 : σ ζ = ζ ^ ℓ :=
    ValuationSubring.smul_eq_pow_of_isFrobeniusAt_of_pow_eq_one A hℓ hA hσ hℓp' hζ.pow_eq_one
  have h2 := cycloChar_spec p σ ζ hζ.pow_eq_one
  set c : ZMod p := ((ExtCitation.cycloChar p σ : (ZMod p)ˣ) : ZMod p) with hc
  have h3 : ζ ^ c.val = ζ ^ (ℓ % p) := by
    rw [← h2, h1]
    conv_lhs => rw [← Nat.mod_add_div ℓ p]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have h4 : c.val = ℓ % p := hζ.pow_inj (ZMod.val_lt c) (Nat.mod_lt ℓ hp.pos) h3
  have h5 : c = (ℓ : ZMod p) := by
    apply ZMod.val_injective
    rw [h4, ZMod.val_natCast]
  rw [coe_cycloK_apply, ← hc, h5, map_natCast]

theorem cycloK_eq_one_of_mem_inertiaSubgroupIn (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    cycloK p κ σ = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot p
  have hℓp' : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)
  have h1 : σ ζ = ζ :=
    ValuationSubring.smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one A hℓ hA hσ hℓp' hζ.pow_eq_one
  exact cycloK_eq_one_of_cycloChar_eq_one p κ
    (ExtCitation.cycloChar_eq_one_of_apply_eq_self_of_isPrimitiveRoot p σ hζ h1)

end Cyclo

section Twist

variable {κ : Type} [Field κ]

noncomputable def scalarGL : κˣ →* GL (Fin 2) κ :=
  Units.map (Matrix.scalar (Fin 2) : κ →+* Matrix (Fin 2) (Fin 2) κ).toMonoidHom

theorem val_scalarGL (u : κˣ) :
    ((scalarGL u : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ) = Matrix.scalar (Fin 2) (u : κ) :=
  rfl

theorem scalarGL_mul_comm (u : κˣ) (g : GL (Fin 2) κ) : scalarGL u * g = g * scalarGL u := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_scalarGL]
  exact (Matrix.scalar_commute (u : κ) (fun r => Commute.all _ r) (g : Matrix (Fin 2) (Fin 2) κ)).eq

variable (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* κˣ) (m : ℕ)
  (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ)

noncomputable def twist : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ where
  toFun σ := scalarGL (χ σ ^ m) * ρ₀ σ
  map_one' := by rw [map_one, one_pow, map_one, map_one, one_mul]
  map_mul' σ τ := by
    rw [map_mul, mul_pow, map_mul, map_mul]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc, scalarGL_mul_comm, mul_assoc]

theorem twist_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    twist χ m ρ₀ σ = scalarGL (χ σ ^ m) * ρ₀ σ :=
  rfl

theorem val_twist (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((twist χ m ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ) =
      (((χ σ : κˣ) : κ) ^ m) • ((ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ) := by
  rw [twist_apply, Units.val_mul, val_scalarGL, Units.val_pow_eq_pow_val, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem trace_twist (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Matrix.trace (twist χ m ρ₀ σ).val = (((χ σ : κˣ) : κ) ^ m) * Matrix.trace (ρ₀ σ).val := by
  rw [val_twist, Matrix.trace_smul, smul_eq_mul]

theorem det_twist (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Matrix.det (twist χ m ρ₀ σ).val = (((χ σ : κˣ) : κ) ^ (2 * m)) * Matrix.det (ρ₀ σ).val := by
  rw [val_twist, Matrix.det_smul, Fintype.card_fin, ← pow_mul, mul_comm m 2]

theorem twist_eq_one {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (h1 : χ σ = 1) (h2 : ρ₀ σ = 1) :
    twist χ m ρ₀ σ = 1 := by
  rw [twist_apply, h1, one_pow, map_one, h2, one_mul]

theorem galoisFactorsThroughFiniteLevel_twist (hχ : GaloisFactorsThroughFiniteLevel χ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ₀) : GaloisFactorsThroughFiniteLevel (twist χ m ρ₀) := by
  obtain ⟨L₁, hL₁, h₁⟩ := hχ
  obtain ⟨L₂, hL₂, h₂⟩ := hρ
  haveI := hL₁
  haveI := hL₂
  refine ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, fun σ hσ => ?_⟩
  refine twist_eq_one χ m ρ₀ (h₁ σ fun x hx => hσ x ?_) (h₂ σ fun x hx => hσ x ?_)
  · exact (le_sup_left : L₁ ≤ L₁ ⊔ L₂) hx
  · exact (le_sup_right : L₂ ≤ L₁ ⊔ L₂) hx

end Twist

section OddVanishing

variable (κ : Type) [Field κ]

theorem binarySubst_neg_one_of_mem {n : ℕ} {F : MvPolynomial (Fin 2) κ} (hF : F ∈ BinaryForm κ n) :
    binarySubst κ (-1 : Matrix (Fin 2) (Fin 2) ℤ) F = ((-1 : κ) ^ n) • F := by
  classical
  have hX : ∀ j : Fin 2,
      (∑ i : Fin 2, MvPolynomial.C ((((-1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : κ)) * MvPolynomial.X i :
        MvPolynomial (Fin 2) κ) = -MvPolynomial.X j := by
    intro j
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp
  have hsubst : binarySubst κ (-1 : Matrix (Fin 2) (Fin 2) ℤ) =
      MvPolynomial.aeval (fun j : Fin 2 => -(MvPolynomial.X j : MvPolynomial (Fin 2) κ)) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    rw [binarySubst_X, MvPolynomial.aeval_X, hX]
  rw [MvPolynomial.mem_homogeneousSubmodule] at hF
  rw [hsubst]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero h)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  have hprod : (d.prod fun i k => (-(MvPolynomial.X i : MvPolynomial (Fin 2) κ)) ^ k) =
      (d.prod fun _ k => ((-1 : MvPolynomial (Fin 2) κ)) ^ k) * d.prod fun i k => MvPolynomial.X i ^ k := by
    rw [← Finsupp.prod_mul]
    refine Finsupp.prod_congr fun i _ => ?_
    rw [← mul_pow, neg_one_mul]
  have hsign : (d.prod fun _ k => ((-1 : MvPolynomial (Fin 2) κ)) ^ k) = (-1 : MvPolynomial (Fin 2) κ) ^ n := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hdeg]
  rw [hprod, hsign, MvPolynomial.monomial_eq, MvPolynomial.smul_eq_C_mul, map_pow, map_neg, map_one]
  ring

variable (N n : ℕ)

noncomputable abbrev ρSym : Representation κ (Gamma0 N) ↥(BinaryForm κ n) :=
  (binaryFormRepSL κ n).comp (Gamma0 N).subtype

theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  simp

def negOne : Gamma0 N := ⟨-1, neg_one_mem_Gamma0 N⟩

theorem negOne_mul_comm (g : Gamma0 N) : g * negOne N = negOne N * g := by
  apply Subtype.ext
  change (g : SL(2, ℤ)) * (-1) = (-1) * (g : SL(2, ℤ))
  rw [mul_neg_one, neg_one_mul]

theorem ρSym_negOne (v : ↥(BinaryForm κ n)) : ρSym κ N n (negOne N) v = ((-1 : κ) ^ n) • v := by
  apply Subtype.ext
  change binarySubst κ (((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) (v : MvPolynomial (Fin 2) κ) =
    (((-1 : κ) ^ n) • v : ↥(BinaryForm κ n))
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Submodule.coe_smul]
  exact binarySubst_neg_one_of_mem κ v.2

theorem coeffH1_eq_zero_of_odd (h2 : (2 : κ) ≠ 0) (hn : Odd n) (x : coeffH1 (ρSym κ N n)) : x = 0 := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
  rw [coeffH1Mk_eq_zero_iff]
  have hneg : ∀ w : ↥(BinaryForm κ n), ρSym κ N n (negOne N) w = -w := fun w => by
    rw [ρSym_negOne, hn.neg_one_pow, neg_one_smul κ w]
  have hz := z.2

  have key : ∀ g : Gamma0 N,
      (2 : κ) • (z : Gamma0 N → ↥(BinaryForm κ n)) g =
        (z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N) -
          ρSym κ N n g ((z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N)) := by
    intro g
    have h1 := hz g (negOne N)
    have h2' := hz (negOne N) g
    rw [← negOne_mul_comm N g, h1, hneg] at h2'

    have e1 : (z : Gamma0 N → ↥(BinaryForm κ n)) g +
        ρSym κ N n g ((z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N)) +
        (z : Gamma0 N → ↥(BinaryForm κ n)) g = (z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N) := by
      rw [h2']
      abel
    rw [two_smul, eq_sub_iff_add_eq]
    convert e1 using 1
    abel
  refine (mem_coeffCoboundaries_iff _ _).mpr
    ⟨-((2 : κ)⁻¹ • (z : Gamma0 N → ↥(BinaryForm κ n)) (negOne N)), funext fun g => ?_⟩
  have hhalf : (2 : κ)⁻¹ • ((2 : κ) • (z : Gamma0 N → ↥(BinaryForm κ n)) g) =
      (z : Gamma0 N → ↥(BinaryForm κ n)) g := by
    rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [map_neg, map_smul, neg_sub_neg]
  conv_rhs => rw [← hhalf, key g, smul_sub]

end OddVanishing

end DeligneModPAssembly

open DeligneModPAssembly in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S₀ : Set ℕ) (n : ℕ)
    (κ : Type) [Field κ] [CharP κ p] (φ : integralClosure ℤ ℂ →+* κ) (lam : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S₀ lam) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val = lam ℓ) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : κ) ^ (n + 1)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨μ, hμocc, hμeq⟩ :=
    HeckeEis.exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom
      p N S₀ n κ φ lam hocc

  obtain ⟨M, mu, hMdvd, hmuocc, hmueq⟩ :=
    HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL
      p N ∅ n κ μ hμocc
  have hM0 : M ≠ 0 := by
    intro h
    rw [h, zero_dvd_iff] at hMdvd
    exact mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hp.ne_zero) hMdvd
  haveI : NeZero M := ⟨hM0⟩
  have hgoodM : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ¬ ℓ ∣ M := by
    intro ℓ hℓ hℓN hℓp h
    rcases (Nat.Prime.dvd_mul hℓ).mp (h.trans hMdvd) with h1 | h2
    · exact hℓN h1
    · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h2))

  obtain ⟨ρ₀, hfin₀, htr₀, hdet₀, hunr₀⟩ :=
    GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom p M (insert p ∅) κ φ mu hmuocc

  refine ⟨twist (cycloK p κ) (n / 2) ρ₀, ?_, ?_, ?_, ?_⟩
  · exact galoisFactorsThroughFiniteLevel_twist _ _ _ (galoisFactorsThroughFiniteLevel_cycloK p κ) hfin₀
  · intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
    have hℓM := hgoodM ℓ hℓ hℓN hℓp
    have hℓins : ℓ ∉ insert p (∅ : Set ℕ) := by
      rw [Set.mem_insert_iff]
      rintro (h | h)
      · exact hℓp h
      · exact h
    rw [trace_twist, coe_cycloK_of_isFrobeniusAt p κ ℓ hℓ hℓp A hA σ hσ,
      htr₀ ℓ hℓ hℓM hℓins hℓp A hA σ hσ, ← hmueq ℓ hℓ hℓN hℓp (Set.notMem_empty ℓ),
      hμeq ℓ hℓ hℓN hℓS]
  · intro ℓ hℓ hℓN hℓp A hA σ hσ
    have hℓM := hgoodM ℓ hℓ hℓN hℓp
    rw [det_twist, coe_cycloK_of_isFrobeniusAt p κ ℓ hℓ hℓp A hA σ hσ, hdet₀ ℓ hℓ hℓM hℓp A hA σ hσ,
      ← pow_succ]

    by_cases hp2 : p = 2
    ·
      subst hp2
      have hℓodd : ℓ % 2 = 1 := (hℓ.eq_two_or_odd).resolve_left hℓp
      have hℓone : (ℓ : κ) = 1 := by
        rw [CharP.cast_eq_mod κ 2 ℓ, hℓodd, Nat.cast_one]
      rw [hℓone, one_pow, one_pow]
    ·
      have h2 : (2 : κ) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : κ) = 0 := by exact_mod_cast h
        rw [CharP.cast_eq_zero_iff κ p] at h'
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      have hn : Even n := by
        by_contra hodd
        rw [Nat.not_even_iff_odd] at hodd
        obtain ⟨x, hx, -⟩ := hocc
        exact hx (coeffH1_eq_zero_of_odd κ N n h2 hodd x)
      rw [Nat.two_mul_div_two_of_even hn]
  · intro ℓ hℓ hℓN hℓp A hA σ hσ
    have hℓM := hgoodM ℓ hℓ hℓN hℓp
    exact twist_eq_one _ _ _ (cycloK_eq_one_of_mem_inertiaSubgroupIn p κ ℓ hℓ hℓp A hA σ hσ)
      (hunr₀ ℓ hℓ hℓM hℓp A hA σ hσ)

end S_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom
end P2MW
export P2MW.S_GaloisRep_exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom (solution)

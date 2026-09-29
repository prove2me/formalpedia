-- Prove2me | solution 1 for GaloisRep.exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/19d7926b-5d27-51ee-a973-812cf82bfdfb

import Mathlib
import Definitions.Def_GaloisRep_DeligneOrdinaryShape
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra
import Theorems.Thm_GaloisRep_exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal
import Theorems.Thm_MonoidHom_exists_finrank_two_trace_eq_add_det_eq_mul_of_mem_range
import Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker
import Theorems.Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow
p2m_attr_erase "instance" "HeckeEis.instFiniteProjLineCusps ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule TateModule.instModule TateModule.instSMul ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular HeckeEis.instAddCommGroupCoeffH1 HeckeEis.instModuleCoeffH1 CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CohCarrier.GammaHLower_finiteIndex FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk ModularCurve.ProjectiveLine.map_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HeckeEis.binaryFormRep_apply_coe HeckeEis.gamma0NebenRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CuspForm

namespace GalFinAssembly

abbrev Γℚ : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

section Powers

variable {R : Type*} [CommRing R]

theorem mul_self_fin_two (M : Matrix (Fin 2) (Fin 2) R) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem pow_add_two_fin_two (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    M ^ (n + 2) = M.trace • M ^ (n + 1) - M.det • M ^ n := by
  rw [pow_succ, pow_succ, mul_assoc, mul_self_fin_two, mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, ← pow_succ]

theorem trace_pow_mem (B : Subring R) (M : Matrix (Fin 2) (Fin 2) R) (htr : M.trace ∈ B)
    (hdet : M.det ∈ B) (n : ℕ) : (M ^ n).trace ∈ B := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [pow_zero, Matrix.trace_one, Fintype.card_fin]
      exact_mod_cast natCast_mem B 2
    | 1 => rw [pow_one]; exact htr
    | n + 2 =>
      rw [pow_add_two_fin_two, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
        smul_eq_mul, smul_eq_mul]
      exact B.sub_mem (B.mul_mem htr (ih (n + 1) (by omega)))
        (B.mul_mem hdet (ih n (by omega)))

theorem det_pow_mem (B : Subring R) (M : Matrix (Fin 2) (Fin 2) R) (hdet : M.det ∈ B) (n : ℕ) :
    (M ^ n).det ∈ B := by
  rw [Matrix.det_pow]; exact B.pow_mem hdet n

end Powers

section Plane

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem linearMap_mul_self (hV : Module.finrank Ω V = 2) (f : V →ₗ[Ω] V) :
    f * f = LinearMap.trace Ω V f • f - LinearMap.det f • (1 : V →ₗ[Ω] V) := by
  haveI : Module.Finite Ω V := Module.finite_of_finrank_eq_succ hV
  let b := Module.finBasisOfFinrankEq Ω V hV
  apply (LinearMap.toMatrixAlgEquiv b).injective
  rw [map_mul, map_sub, map_smul, map_smul, map_one, LinearMap.trace_eq_matrix_trace Ω b,
    ← LinearMap.det_toMatrix b]
  exact mul_self_fin_two (LinearMap.toMatrixAlgEquiv b f)

theorem trace_eq_of_eigenvector (hV : Module.finrank Ω V = 2) (f : V ≃ₗ[Ω] V) {w : V}
    (hw : w ≠ 0) {a : Ω} (ha : f w = a • w) :
    a ≠ 0 ∧ LinearMap.trace Ω V f * a = a * a + LinearMap.det (f : V →ₗ[Ω] V) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at ha
    exact hw ha
  refine ⟨ha0, ?_⟩
  have h := congrArg (fun g : V →ₗ[Ω] V => g w) (linearMap_mul_self hV (f : V →ₗ[Ω] V))
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, LinearEquiv.coe_coe] at h
  rw [ha, map_smul, ha, smul_smul, smul_smul, ← sub_smul] at h
  have h' := sub_eq_zero.mpr h
  rw [← sub_smul, smul_eq_zero] at h'
  rcases h' with h' | h'
  · linear_combination -h'
  · exact absurd h' hw

end Plane

section Descent

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]
  (K : Type) [Field K] [Finite K] (ι : K →+* Ω)
  (V : Type) [AddCommGroup V] [Module Ω V]

theorem descend (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2)
    (ρ : Γℚ →* (V ≃ₗ[Ω] V)) (hfin : Finite ρ.range)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module K V₀) (ρ₀ : Γℚ →* (V₀ ≃ₗ[K] V₀)),
      Module.finrank K V₀ = 2 ∧ ρ.ker ≤ ρ₀.ker ∧
      (∀ σ, ι (LinearMap.trace K V₀ (ρ₀ σ).toLinearMap) = LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap) := by
  by_cases hirr : ∀ W : Submodule Ω V, (∀ σ, ∀ v ∈ W, ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤
  ·
    have hcyc : ModularCurve.CyclotomicDeterminant 0 p ρ := by
      intro ℓ hℓ hdvd
      exact absurd (by rw [zero_mul]; exact dvd_zero ℓ) hdvd
    obtain ⟨V₀, _, _, ρ₀, h2, -, hker, htr₀, hdet₀, -⟩ :=
      ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite (K := ℚ)
        (L := AlgebraicClosure ℚ) 0 p Ω K ι V ρ hp hV hfin hirr htr hdet hcyc
    exact ⟨V₀, _, _, ρ₀, h2, hker, htr₀, hdet₀⟩
  ·
    push Not at hirr
    obtain ⟨W, hWstab, hWbot, hWtop⟩ := hirr
    haveI : Module.Finite Ω V := Module.finite_of_finrank_eq_succ hV
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
    have hW1 : Module.finrank Ω W = 1 := by
      have hlt : Module.finrank Ω W < 2 := by
        rw [← hV, ← finrank_top Ω V]
        exact Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hWtop)
      have hpos : 0 < Module.finrank Ω W := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        exact ⟨⟨w, hwW⟩, fun h => hw0 (congrArg Subtype.val h)⟩
      omega

    have hev : ∀ σ, ∃ a : Ω, ρ σ w = a • w := by
      intro σ
      have hmem : ρ σ w ∈ W := hWstab σ w hwW
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwW⟩ : W)
        (fun h => hw0 (congrArg Subtype.val h))).mp hW1 ⟨ρ σ w, hmem⟩
      exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
    choose a ha using hev
    have hane : ∀ σ, a σ ≠ 0 := fun σ => (trace_eq_of_eigenvector hV (ρ σ) hw0 (ha σ)).1
    have hmul : ∀ σ τ, a (σ * τ) = a σ * a τ := by
      intro σ τ
      have h1 : ρ (σ * τ) w = (a σ * a τ) • w := by
        rw [map_mul, LinearEquiv.mul_apply, ha τ, map_smul, ha σ, smul_smul, mul_comm]
      rw [ha] at h1
      exact smul_left_injective Ω hw0 h1
    have hone : a 1 = 1 := by
      have h1 : ρ 1 w = (1 : Ω) • w := by rw [map_one, one_smul]; rfl
      rw [ha] at h1
      exact smul_left_injective Ω hw0 h1
    let χ₁ : Γℚ →* Ωˣ :=
      { toFun := fun σ => Units.mk0 (a σ) (hane σ)
        map_one' := Units.ext hone
        map_mul' := fun σ τ => Units.ext (hmul σ τ) }
    have hχ₁ : ∀ σ, (χ₁ σ : Ω) = a σ := fun σ => rfl
    let δ : Γℚ →* Ωˣ := LinearEquiv.det.comp ρ
    have hδ : ∀ σ, (δ σ : Ω) = LinearMap.det (ρ σ : V →ₗ[Ω] V) := fun σ =>
      LinearEquiv.coe_det (ρ σ)
    let χ₂ : Γℚ →* Ωˣ := δ * χ₁⁻¹
    have hχ₂ : ∀ σ, (χ₂ σ : Ω) * a σ = LinearMap.det (ρ σ : V →ₗ[Ω] V) := by
      intro σ
      change ((δ σ * (χ₁ σ)⁻¹ : Ωˣ) : Ω) * a σ = _
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hχ₁, hδ, inv_mul_cancel_right₀ (hane σ)]
    have htrace : ∀ σ, LinearMap.trace Ω V (ρ σ : V →ₗ[Ω] V) = a σ + χ₂ σ := by
      intro σ
      have h := (trace_eq_of_eigenvector hV (ρ σ) hw0 (ha σ)).2
      rw [← hχ₂ σ] at h
      have h' : (LinearMap.trace Ω V (ρ σ : V →ₗ[Ω] V) - (a σ + χ₂ σ)) * a σ = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp h' with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' (hane σ)
    have hdet' : ∀ σ, LinearMap.det (ρ σ : V →ₗ[Ω] V) = a σ * χ₂ σ := fun σ => by
      rw [← hχ₂ σ, mul_comm]
    have hadd : ∀ σ, (χ₁ σ : Ω) + χ₂ σ ∈ ι.range := fun σ => by
      rw [hχ₁, ← htrace]; exact htr σ
    have hmul' : ∀ σ, (χ₁ σ : Ω) * χ₂ σ ∈ ι.range := fun σ => by
      rw [hχ₁, ← hdet']; exact hdet σ
    obtain ⟨V₀, _, _, ρ₀, h2, htriv, htr₀, hdet₀⟩ :=
      MonoidHom.exists_finrank_two_trace_eq_add_det_eq_mul_of_mem_range ι χ₁ χ₂ hadd hmul'
    refine ⟨V₀, _, _, ρ₀, h2, ?_, fun σ => by rw [htr₀, hχ₁, htrace],
      fun σ => by rw [hdet₀, hχ₁, hdet']⟩
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    have ha1 : a σ = 1 := by
      have h1 : ρ σ w = (1 : Ω) • w := by rw [hσ, one_smul]; rfl
      rw [ha] at h1
      exact smul_left_injective Ω hw0 h1
    refine htriv σ (Units.ext (by rw [hχ₁, ha1, Units.val_one])) (Units.ext ?_)
    have h := hχ₂ σ
    rw [ha1, mul_one, hσ] at h
    rw [h, Units.val_one]
    exact LinearMap.det_id

omit [IsAlgClosed Ω] [Finite K] in

theorem toGL {V₀ : Type} [AddCommGroup V₀] [Module K V₀] (h2 : Module.finrank K V₀ = 2)
    (ρ₀ : Γℚ →* (V₀ ≃ₗ[K] V₀)) :
    ∃ ρK : Γℚ →* GL (Fin 2) K, ρ₀.ker ≤ ρK.ker ∧
      (∀ σ, (ρK σ).val.trace = LinearMap.trace K V₀ (ρ₀ σ).toLinearMap) ∧
      (∀ σ, (ρK σ).val.det = LinearMap.det (ρ₀ σ).toLinearMap) := by
  haveI : Module.Finite K V₀ := Module.finite_of_finrank_eq_succ h2
  let b₀ := Module.finBasisOfFinrankEq K V₀ h2
  let ρK : Γℚ →* GL (Fin 2) K :=
    (Units.map (LinearMap.toMatrixAlgEquiv b₀).toMonoidHom).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V₀).symm.toMonoidHom.comp ρ₀)
  have hρK : ∀ σ, (ρK σ).val = LinearMap.toMatrixAlgEquiv b₀ (ρ₀ σ).toLinearMap := fun σ => rfl
  refine ⟨ρK, fun σ hσ => ?_, fun σ => ?_, fun σ => ?_⟩
  · rw [MonoidHom.mem_ker] at hσ ⊢
    change Units.map _ ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V₀).symm (ρ₀ σ)) = 1
    rw [hσ, map_one, map_one]
  · rw [hρK]
    exact (LinearMap.trace_eq_matrix_trace K b₀ _).symm
  · rw [hρK]
    change (LinearMap.toMatrix b₀ b₀ (ρ₀ σ).toLinearMap).det = _
    rw [LinearMap.det_toMatrix b₀]

theorem descendGL (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2)
    (ρ : Γℚ →* (V ≃ₗ[Ω] V)) (hfin : Finite ρ.range)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range) :
    ∃ ρK : Γℚ →* GL (Fin 2) K, ρ.ker ≤ ρK.ker ∧
      (∀ σ, ι (ρK σ).val.trace = LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (ρK σ).val.det = LinearMap.det (ρ σ).toLinearMap) := by
  obtain ⟨V₀, _, _, ρ₀, h2, hker, htr₀, hdet₀⟩ := descend p K ι V hp hV ρ hfin htr hdet
  obtain ⟨ρK, hkerK, htrK, hdetK⟩ := toGL K h2 ρ₀
  exact ⟨ρK, hker.trans hkerK, fun σ => by rw [htrK, htr₀], fun σ => by rw [hdetK, hdet₀]⟩

end Descent

section Main

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (S : Set ℕ) (hSfin : S.Finite)
    (k : ℤ) (kn : ℕ) (hkn : (kn : ℤ) = k)
    (F : Type) [Field F] [CharP F p] (θ : heckeAlgebra N k S →+* F)

theorem frobeniusPowerDense_ker {M : Type} [Group M] (ρ : Γℚ →* M)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (T : Finset ℕ) : FrobeniusPowerDense T ρ.ker := by
  obtain ⟨L₀, hfd₀, hL₀⟩ := hρ
  haveI := hfd₀
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ L₀ (AlgebraicClosure ℚ)
  haveI hfdE : FiniteDimensional ℚ E := normalClosure.is_finiteDimensional ℚ L₀ _
  haveI hNE : Normal ℚ E := normalClosure.normal ℚ L₀ _
  haveI : NumberField E := ⟨⟩
  haveI : IsGalois ℚ E := ⟨⟩
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E).ker ≤ ρ.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    change σ.restrictNormal E = 1 at hσ
    refine hL₀ σ fun x hx => ?_
    have h := AlgEquiv.restrictNormal_commutes σ E ⟨x, IntermediateField.le_normalClosure L₀ hx⟩
    rw [hσ, AlgEquiv.one_apply] at h
    exact h.symm
  exact FrobeniusDensity.frobeniusPowerDense_of_le_ker E hker T

include hSfin in

theorem assemble (K : Type) [Field K] (π : heckeAlgebra N k S →+* K) (θbar : K →+* F)
    (hθbar : ∀ t, θbar (π t) = θ t)
    (L : Type) [Field L] [Finite L] (j : K →+* L) (hpL : (p : L) = 0)
    (ρL : Γℚ →* GL (Fin 2) L) (hfinL : GaloisFactorsThroughFiniteLevel ρL)
    (htrL : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρL σ).val = j (π (heckeAlgebra.T hℓ hℓN hℓS)))
    (hdetL : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρL σ).val = (ℓ : L) ^ (kn - 1)) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val = θ (heckeAlgebra.T hℓ hℓN hℓS)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : F) ^ (kn - 1)) := by
  have hpp : p.Prime := Fact.out
  have hjinj : Function.Injective j := j.injective
  haveI : Finite K := Finite.of_injective j hjinj

  let T : Finset ℕ := hSfin.toFinset ∪ {p} ∪ N.primeFactors
  have hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ T → ¬ ℓ ∣ N ∧ ℓ ∉ S ∧ ℓ ≠ p := by
    intro ℓ hℓ hℓT
    simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Finset.mem_singleton,
      Nat.mem_primeFactors, not_or, not_and] at hℓT
    exact ⟨fun h => hℓT.2 hℓ h (NeZero.ne N), hℓT.1.1, hℓT.1.2⟩
  have hdense : FrobeniusPowerDense T ρL.ker := frobeniusPowerDense_ker ρL hfinL T
  have hrange : ∀ σ, (ρL σ).val.trace ∈ j.range ∧ (ρL σ).val.det ∈ j.range := by
    intro σ
    obtain ⟨ℓ, A, τ, g, n, hℓ, hℓT, hA, hτ, hmem⟩ := hdense σ
    obtain ⟨hℓN, hℓS, hℓp⟩ := hT ℓ hℓ hℓT
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_pow, map_inv, map_inv,
      mul_inv_eq_one] at hmem
    have hval : (ρL σ).val = (ρL g).val * ((ρL τ).val ^ n) * (ρL g)⁻¹.val := by
      rw [← hmem, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
    have htrτ : (ρL τ).val.trace ∈ j.range := ⟨_, (htrL ℓ hℓ hℓN hℓS hℓp A hA τ hτ).symm⟩
    have hdetτ : (ρL τ).val.det ∈ j.range :=
      ⟨((ℓ : ℕ) : K) ^ (kn - 1), by rw [map_pow, map_natCast, hdetL ℓ hℓ hℓN hℓS hℓp A hA τ hτ]⟩
    refine ⟨?_, ?_⟩
    · rw [hval, Matrix.trace_units_conj]
      exact trace_pow_mem j.range _ htrτ hdetτ n
    · rw [hval, Matrix.det_units_conj]
      exact det_pow_mem j.range _ hdetτ n

  let Ω : Type := AlgebraicClosure L
  let ι : K →+* Ω := (algebraMap L Ω).comp j
  have hpΩ : (p : Ω) = 0 := by rw [← map_natCast (algebraMap L Ω), hpL, map_zero]
  let Φ : GL (Fin 2) L →* ((Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv Ω (Fin 2 → Ω)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
        (Matrix.GeneralLinearGroup.map (algebraMap L Ω)))
  have hΦ : ∀ M : GL (Fin 2) L,
      ((Φ M : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) : (Fin 2 → Ω) →ₗ[Ω] (Fin 2 → Ω)) =
        Matrix.toLin' (M.val.map (algebraMap L Ω)) := fun M => rfl
  let ρΩ : Γℚ →* ((Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) := Φ.comp ρL
  have hρΩtr : ∀ σ, LinearMap.trace Ω _ (ρΩ σ).toLinearMap = algebraMap L Ω (ρL σ).val.trace := by
    intro σ
    change LinearMap.trace Ω _ ((Φ (ρL σ) : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) : (Fin 2 → Ω) →ₗ[Ω] _) = _
    rw [hΦ, Matrix.trace_toLin'_eq, AddMonoidHom.map_trace]
  have hρΩdet : ∀ σ, LinearMap.det (ρΩ σ).toLinearMap = algebraMap L Ω (ρL σ).val.det := by
    intro σ
    change LinearMap.det ((Φ (ρL σ) : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) : (Fin 2 → Ω) →ₗ[Ω] _) = _
    rw [hΦ, LinearMap.det_toLin', RingHom.map_det, RingHom.mapMatrix_apply]
  have hV : Module.finrank Ω (Fin 2 → Ω) = 2 := by simp
  have hfinΩ : Finite ρΩ.range := by
    have h : (Set.range ρΩ).Finite := by
      have : Set.range ρΩ = Φ '' Set.range ρL := by
        ext x; simp [ρΩ]
      rw [this]; exact (Set.toFinite _).image _
    exact h.to_subtype
  have htrΩ : ∀ σ, LinearMap.trace Ω _ (ρΩ σ).toLinearMap ∈ ι.range := by
    intro σ
    obtain ⟨x, hx⟩ := (hrange σ).1
    exact ⟨x, by rw [hρΩtr, ← hx]; rfl⟩
  have hdetΩ : ∀ σ, LinearMap.det (ρΩ σ).toLinearMap ∈ ι.range := by
    intro σ
    obtain ⟨x, hx⟩ := (hrange σ).2
    exact ⟨x, by rw [hρΩdet, ← hx]; rfl⟩
  obtain ⟨ρK, hker₀, htr₀, hdet₀⟩ := descendGL p K ι (Fin 2 → Ω) hpΩ hV ρΩ hfinΩ htrΩ hdetΩ
  have hιinj : Function.Injective ι := ι.injective

  have htr₀' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ → (ρK σ).val.trace = π (heckeAlgebra.T hℓ hℓN hℓS) := by
    intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
    apply hιinj
    rw [htr₀, hρΩtr, htrL ℓ hℓ hℓN hℓS hℓp A hA σ hσ]; rfl
  have hdet₀' : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ ℓ → (ρK σ).val.det = ((ℓ : ℕ) : K) ^ (kn - 1) := by
    intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
    apply hιinj
    rw [hdet₀, hρΩdet, hdetL ℓ hℓ hℓN hℓS hℓp A hA σ hσ, map_pow, map_pow, map_natCast,
      map_natCast]

  let ρ : Γℚ →* GL (Fin 2) F := (Matrix.GeneralLinearGroup.map θbar).comp ρK
  have hρ : ∀ σ, (ρ σ).val = θbar.mapMatrix (ρK σ).val := fun σ => rfl
  refine ⟨ρ, ?_, ?_, ?_⟩
  ·
    obtain ⟨L₀, hfd₀, hL₀⟩ := hfinL
    refine ⟨L₀, hfd₀, fun σ hσ => ?_⟩
    have h1 : ρL σ = 1 := hL₀ σ hσ
    have h2 : σ ∈ ρΩ.ker := by
      rw [MonoidHom.mem_ker]
      change Φ (ρL σ) = 1
      rw [h1, map_one]
    have h3 : ρK σ = 1 := (MonoidHom.mem_ker).mp (hker₀ h2)
    change Matrix.GeneralLinearGroup.map θbar (ρK σ) = 1
    rw [h3, map_one]
  · intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
    rw [hρ, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, htr₀' ℓ hℓ hℓN hℓS hℓp A hA σ hσ]
    exact hθbar _
  · intro ℓ hℓ hℓN hℓS hℓp A hA σ hσ
    rw [hρ, ← RingHom.map_det, hdet₀' ℓ hℓ hℓN hℓS hℓp A hA σ hσ, map_pow, map_natCast]

include hpN hSfin hkn in

theorem main :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val = θ (heckeAlgebra.T hℓ hℓN hℓS)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : F) ^ (kn - 1)) := by
  have hpp : p.Prime := Fact.out

  haveI : Module.Finite ℤ (heckeAlgebra N k S) := CuspForm.moduleFinite_heckeAlgebra N k S
  haveI : Algebra.IsIntegral ℤ (heckeAlgebra N k S) := Algebra.IsIntegral.of_finite ℤ _
  haveI h𝔪p : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime θ
  have hp𝔪 : ((p : ℕ) : heckeAlgebra N k S) ∈ RingHom.ker θ := by
    rw [RingHom.mem_ker, map_natCast]; exact CharP.cast_eq_zero F p
  have hcomap : ((RingHom.ker θ).comap (algebraMap ℤ (heckeAlgebra N k S))).IsMaximal := by
    have h : (RingHom.ker θ).comap (algebraMap ℤ (heckeAlgebra N k S)) = Ideal.span {(p : ℤ)} := by
      ext n
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_span_singleton, eq_intCast,
        map_intCast]
      exact CharP.intCast_eq_zero_iff F p n
    rw [h]; exact Int.ideal_span_isMaximal_of_prime p
  haveI h𝔪max : (RingHom.ker θ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hcomap

  obtain ⟨L, _instL, _instLfin, j, ρL, hfinL, htrL, hdetL⟩ :=
    GaloisRep.exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal p N hpN S hSfin k kn hkn
      (RingHom.ker θ) h𝔪max hp𝔪
  have hpL : (p : L) = 0 := by
    rw [← map_natCast j, ← map_natCast (Ideal.Quotient.mk (RingHom.ker θ)),
      Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔪, map_zero]
  letI instK : Field (heckeAlgebra N k S ⧸ RingHom.ker θ) := Ideal.Quotient.field _
  exact assemble p N S hSfin k kn F θ (heckeAlgebra N k S ⧸ RingHom.ker θ)
    (Ideal.Quotient.mk (RingHom.ker θ)) (Ideal.Quotient.lift (RingHom.ker θ) θ fun a ha => ha)
    (fun t => Ideal.Quotient.lift_mk _ θ _) L j hpL ρL hfinL htrL hdetL

end Main

end GalFinAssembly

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (S : Set ℕ) (hSfin : S.Finite)
    (k : ℤ) (kn : ℕ) (hkn : (kn : ℤ) = k)
    (F : Type) [Field F] [CharP F p] (θ : heckeAlgebra N k S →+* F) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val = θ (heckeAlgebra.T hℓ hℓN hℓS)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.det (ρ σ).val = (ℓ : F) ^ (kn - 1)) :=
  GalFinAssembly.main p N hpN S hSfin k kn hkn F θ

end S_GaloisRep_exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow
end P2MW
export P2MW.S_GaloisRep_exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow (solution)

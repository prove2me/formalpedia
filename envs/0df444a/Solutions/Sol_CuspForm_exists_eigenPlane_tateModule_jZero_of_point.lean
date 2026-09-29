-- Prove2me | solution 1 for CuspForm.exists_eigenPlane_tateModule_jZero_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/493ac752-1927-5e9c-a3ad-6a7344eb189b

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_EllipticCurve_TateModule
import Theorems.Thm_ModularCurve_rationalRankTwoCyclotomic_family
import Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jZero
import Theorems.Thm_ModularCurve_rep_tateModule_jZero_comm
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_exists_ringHom_rationalHeckeAlgebra_extends_heckeChar
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_eigenPlane_tateModule_jZero_of_point
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped TensorProduct

namespace EigenPlaneOfPoint

section Socle

theorem exists_ann_of_ne_top (K : Type*) {B : Type*} [Field K] [CommRing B] [Algebra K B]
    [Module.Finite K B] (I : Ideal B) (hI : I ≠ ⊤) :
    ∃ a : B, a ≠ 0 ∧ ∀ m ∈ I, m * a = 0 := by
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite K B

  let f : ℕ →o (Ideal B)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (I ^ n), fun m n h =>
      OrderDual.toDual_le_toDual.mpr (Ideal.pow_le_pow_right h)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  have hstab : I ^ n = I ^ (n + 1) := by
    have h := hn (n + 1) (Nat.le_succ n)
    exact OrderDual.toDual.injective h

  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (I ^ n)
      (IsNoetherian.noetherian _) (by
        rw [Ideal.smul_eq_mul, ← pow_succ']
        exact hstab.le)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hI
    rw [zero_sub] at hr1
    have h1 : (1 : B) ∈ I := by simpa using I.neg_mem hr1
    exact (Ideal.eq_top_iff_one I).mpr h1

  have hex : ∃ j : ℕ, ∀ x ∈ I ^ j, r * x = 0 := ⟨n, fun x hx => hr x hx⟩
  set j := Nat.find hex with hj_def
  have hj : ∀ x ∈ I ^ j, r * x = 0 := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    have h1 : (1 : B) ∈ I ^ j := by rw [h0, pow_zero, Ideal.one_eq_top]; trivial
    have := hj 1 h1
    rw [mul_one] at this
    exact hr0 this
  obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hlt : j' < j := by omega
  have hnot := Nat.find_min hex hlt
  push Not at hnot
  obtain ⟨x, hx, hrx⟩ := hnot
  refine ⟨r * x, hrx, fun m hm => ?_⟩
  have hmx : m * x ∈ I ^ j := by
    rw [hj', pow_succ']
    exact Ideal.mul_mem_mul hm hx
  calc m * (r * x) = r * (m * x) := by ring
    _ = 0 := hj _ hmx

end Socle

section Engine

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {A : Type*} [CommRing A] [Algebra k A] [Module A V] [IsScalarTower k A V]
variable (ι : A →ₐ[k] Module.End k V) (hι : ∀ (a : A) (v : V), ι a v = a • v)
variable (b : Module.Basis (Fin 2) A V)
variable (Λ : A →ₐ[k] K)

def ΛB : (K ⊗[k] A) →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) Λ (fun _ _ => Commute.all _ _)

theorem ΛB_tmul (c : K) (a : A) : ΛB Λ (c ⊗ₜ[k] a) = c * Λ a := by
  rw [ΛB, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]

def Θ : (K ⊗[k] A) →ₐ[K] Module.End K ((K ⊗[k] V)) :=
  Algebra.TensorProduct.lift (Algebra.ofId K _) ((Module.End.baseChangeHom k K V).comp ι)
    (fun c x => Algebra.commute_algebraMap_left c _)

theorem Θ_tmul_eq (c : K) (a : A) : Θ ι (c ⊗ₜ[k] a) = c • (ι a).baseChange K := by
  rw [Θ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, ← Algebra.smul_def]
  rfl

theorem Θ_one_tmul (a : A) : Θ ι ((1 : K) ⊗ₜ[k] a) = (ι a).baseChange K := by
  rw [Θ_tmul_eq, one_smul]

include hι in
theorem Θ_tmul_tmul (c : K) (a : A) (c' : K) (v : V) :
    Θ ι (c ⊗ₜ[k] a) (c' ⊗ₜ[k] v) = (c * c') ⊗ₜ[k] (a • v) := by
  rw [Θ_tmul_eq, LinearMap.smul_apply, LinearMap.baseChange_tmul, hι, TensorProduct.smul_tmul',
    smul_eq_mul]

def R (i : Fin 2) : (K ⊗[k] V) →ₗ[K] (K ⊗[k] A) :=
  ((b.coord i).restrictScalars k).baseChange K

theorem R_tmul (i : Fin 2) (c : K) (v : V) : R (K := K) b i (c ⊗ₜ[k] v) = c ⊗ₜ[k] (b.repr v i) := by
  rw [R, LinearMap.baseChange_tmul]
  rfl

include hι in

theorem R_Θ (i : Fin 2) (x : (K ⊗[k] A)) (w : (K ⊗[k] V)) :
    R (K := K) b i (Θ ι x w) = x * R (K := K) b i w := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c' v =>
      rw [Θ_tmul_tmul ι hι, R_tmul, R_tmul, Algebra.TensorProduct.tmul_mul_tmul, map_smul,
        Finsupp.smul_apply, smul_eq_mul]
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, mul_add]
  | add x y hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, add_mul]

def Bv (j : Fin 2) : (K ⊗[k] V) := (1 : K) ⊗ₜ[k] b j

theorem R_Bv (i j : Fin 2) :
    (R (K := K) b i (Bv (K := K) b j) : K ⊗[k] A) = if i = j then 1 else 0 := by
  rw [Bv, R_tmul, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp; rfl
  · rw [if_neg (Ne.symm h), if_neg h, TensorProduct.tmul_zero]

include hι in

theorem unique_coord (x₀ x₁ : (K ⊗[k] A))
    (h : Θ ι x₀ (Bv (K := K) b 0) + Θ ι x₁ (Bv (K := K) b 1) = 0) : x₀ = 0 ∧ x₁ = 0 := by
  have h0 := congrArg (R (K := K) b 0) h
  have h1 := congrArg (R (K := K) b 1) h
  rw [map_add, R_Θ ι hι, R_Θ ι hι, R_Bv, R_Bv, map_zero] at h0 h1
  simp at h0 h1
  exact ⟨h0, h1⟩

variable {G : Type*} [Group G] (ρ : G →* Module.End k V)
variable (hρ : ∀ (σ : G) (a : A), ι a * ρ σ = ρ σ * ι a)

abbrev ρK (σ : G) : Module.End K ((K ⊗[k] V)) := (ρ σ).baseChange K

def M (σ : G) : Matrix (Fin 2) (Fin 2) A := fun i j => b.repr (ρ σ (b j)) i

include hρ in
theorem Θ_comm (σ : G) (x : (K ⊗[k] A)) : Θ ι x * ρK (K := K) ρ σ = ρK (K := K) ρ σ * Θ ι x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    rw [Θ_tmul_eq, smul_mul_assoc, mul_smul_comm, ρK, ← LinearMap.baseChange_mul,
      ← LinearMap.baseChange_mul, hρ]
  | add x y hx hy => rw [map_add, add_mul, mul_add, hx, hy]

include hι in
theorem ρK_Bv (σ : G) (j : Fin 2) :
    ρK (K := K) ρ σ (Bv (K := K) b j) = ∑ i, Θ ι ((1 : K) ⊗ₜ[k] M b ρ σ i j) (Bv (K := K) b i) := by
  rw [ρK, Bv, LinearMap.baseChange_tmul]
  conv_lhs => rw [← b.sum_repr (ρ σ (b j))]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Bv, Θ_tmul_tmul ι hι, mul_one]
  rfl

variable (a₀ : (K ⊗[k] A)) (ha₀ : ∀ m : (K ⊗[k] A), ΛB Λ m = 0 → m * a₀ = 0)

include ha₀ in
theorem mul_a₀ (m : (K ⊗[k] A)) : m * a₀ = ΛB Λ m • a₀ := by
  have h : (m - algebraMap K ((K ⊗[k] A)) (ΛB Λ m)) * a₀ = 0 := by
    apply ha₀
    rw [map_sub, AlgHom.commutes]
    simp
  rw [sub_mul, sub_eq_zero] at h
  rw [h, Algebra.smul_def]

def w (j : Fin 2) : (K ⊗[k] V) := Θ ι a₀ (Bv (K := K) b j)

include hι hρ ha₀ in

theorem ρK_w (σ : G) (j : Fin 2) :
    ρK (K := K) ρ σ (w ι b a₀ j) = ∑ i, Λ (M b ρ σ i j) • w ι b a₀ i := by
  have hc := congrArg (fun f => f (Bv (K := K) b j)) (Θ_comm ι ρ hρ σ a₀ (K := K))
  simp only [Module.End.mul_apply] at hc
  rw [w, ← hc, ρK_Bv ι hι b ρ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Module.End.mul_apply, ← map_mul, mul_comm, mul_a₀ Λ a₀ ha₀, ΛB_tmul, one_mul, map_smul,
    LinearMap.smul_apply, w]

include ha₀ in

theorem ΘA_w (a : A) (j : Fin 2) :
    (ι a).baseChange K (w ι b a₀ j) = Λ a • w ι b a₀ (K := K) j := by
  rw [← Θ_one_tmul, w, ← Module.End.mul_apply, ← map_mul, mul_a₀ Λ a₀ ha₀, ΛB_tmul, one_mul,
    map_smul, LinearMap.smul_apply]

def W : Submodule K ((K ⊗[k] V)) := Submodule.span K (Set.range (w ι b a₀ (K := K)))

theorem w_mem (j : Fin 2) : w ι b a₀ (K := K) j ∈ W ι b a₀ (K := K) :=
  Submodule.subset_span ⟨j, rfl⟩

include Λ hι hρ ha₀ in
theorem W_stable (σ : G) : ∀ x ∈ W ι b a₀ (K := K), ρK (K := K) ρ σ x ∈ W ι b a₀ (K := K) := by
  have h : W ι b a₀ (K := K) ≤ (W ι b a₀ (K := K)).comap (ρK (K := K) ρ σ) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ρK_w ι hι b Λ ρ hρ a₀ ha₀]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (w_mem ι b a₀ i)
  intro x hx
  exact h hx

include ha₀ in
theorem W_hecke (a : A) : ∀ x ∈ W ι b a₀ (K := K), (ι a).baseChange K x = Λ a • x := by
  have h : W ι b a₀ (K := K) ≤ Module.End.eigenspace ((ι a).baseChange K) (Λ a) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
    exact ΘA_w ι b Λ a₀ ha₀ a j
  intro x hx
  exact Module.End.mem_eigenspace_iff.mp (h hx)

variable (ha₀0 : a₀ ≠ 0)

include hι ha₀0 in
theorem w_linearIndependent : LinearIndependent K (w ι b a₀ (K := K)) := by
  refine Fintype.linearIndependent_iff.mpr fun c hc j => ?_
  rw [Fin.sum_univ_two] at hc
  have e : ∀ i, c i • w ι b a₀ (K := K) i = Θ ι (c i • a₀) (Bv (K := K) b i) := fun i => by
    rw [w, map_smul, LinearMap.smul_apply]
  rw [e, e] at hc
  obtain ⟨h0, h1⟩ := unique_coord ι hι b _ _ hc
  have key : ∀ i, c i • a₀ = 0 → c i = 0 := fun i hi => by
    by_contra hne
    apply ha₀0
    have := congrArg (fun x => (c i)⁻¹ • x) hi
    simpa [smul_smul, inv_mul_cancel₀ hne] using this
  fin_cases j
  · exact key 0 h0
  · exact key 1 h1

include hι ha₀0 in
theorem finrank_W : Module.finrank K (W ι b a₀ (K := K)) = 2 := by
  rw [W, finrank_span_eq_card (w_linearIndependent ι hι b a₀ ha₀0), Fintype.card_fin]

def bW : Module.Basis (Fin 2) K (W ι b a₀ (K := K)) :=
  Module.Basis.span (w_linearIndependent ι hι b a₀ ha₀0)

theorem bW_apply (j : Fin 2) : (bW ι hι b a₀ ha₀0 j : (K ⊗[k] V)) = w ι b a₀ (K := K) j :=
  congrArg Subtype.val (Module.Basis.span_apply (w_linearIndependent ι hι b a₀ ha₀0) j)

include ha₀0 in

theorem trace_W (σ : G) :
    LinearMap.trace K (W ι b a₀ (K := K))
        ((ρK (K := K) ρ σ).restrict (W_stable ι hι b Λ ρ hρ a₀ ha₀ σ)) =
      Λ (M b ρ σ 0 0) + Λ (M b ρ σ 1 1) := by
  classical
  set f := (ρK (K := K) ρ σ).restrict (W_stable ι hι b Λ ρ hρ a₀ ha₀ σ)
  have hf : ∀ j, f (bW ι hι b a₀ ha₀0 j) = ∑ i, Λ (M b ρ σ i j) • bW ι hι b a₀ ha₀0 i := by
    intro j
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, bW_apply, ρK_w ι hι b Λ ρ hρ a₀ ha₀, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, bW_apply]
  rw [LinearMap.trace_eq_matrix_trace K (bW ι hι b a₀ ha₀0), Matrix.trace_fin_two,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hf, hf, Module.Basis.repr_sum_self,
    Module.Basis.repr_sum_self]

def ρA (σ : G) : V →ₗ[A] V where
  toFun := ρ σ
  map_add' := map_add _
  map_smul' a v := by
    have h := congrArg (fun f => f v) (hρ σ a)
    simp only [Module.End.mul_apply] at h
    rw [RingHom.id_apply, ← hι, ← hι, h]

@[scoped simp] theorem ρA_apply (σ : G) (v : V) : ρA ι hι ρ hρ σ v = ρ σ v := rfl

theorem toMatrix_ρA (σ : G) : LinearMap.toMatrix b b (ρA ι hι ρ hρ σ) = M b ρ σ := by
  ext i j
  rw [LinearMap.toMatrix_apply, ρA_apply]
  rfl

theorem cayley_hamilton_two (X : Matrix (Fin 2) (Fin 2) A) :
    X * X - (X 0 0 + X 1 1) • X + (X 0 0 * X 1 1 - X 0 1 * X 1 0) • (1 : Matrix (Fin 2) (Fin 2) A)
      = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

include hι hρ in

theorem trace_M_eq (σ : G) (t : A) (ℓ : ℕ)
    (hES : ∀ v : V, ρ σ (ρ σ v) - ι t (ρ σ v) + (ℓ : k) • v = 0)
    (hdet : b.repr (ρ σ (b 0)) 0 * b.repr (ρ σ (b 1)) 1
      - b.repr (ρ σ (b 1)) 0 * b.repr (ρ σ (b 0)) 1 = ℓ) :
    M b ρ σ 0 0 + M b ρ σ 1 1 = t := by
  classical
  set X := M b ρ σ with hX

  have hEnd : ρA ι hι ρ hρ σ * ρA ι hι ρ hρ σ - t • ρA ι hι ρ hρ σ
      + (ℓ : A) • (1 : Module.End A V) = 0 := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, ρA_apply, Module.End.one_apply]
    rw [← hι t, show ((ℓ : ℕ) : A) = algebraMap k A (ℓ : k) from (map_natCast _ ℓ).symm,
      algebraMap_smul]
    exact hES v
  have hMat : X * X - t • X + (ℓ : A) • (1 : Matrix (Fin 2) (Fin 2) A) = 0 := by
    have h := congrArg (LinearMap.toMatrix b b) hEnd
    rw [map_add, map_sub, LinearMap.toMatrix_mul, map_smul, map_smul, LinearMap.toMatrix_one,
      toMatrix_ρA, map_zero] at h
    exact h
  have hdet' : X 0 0 * X 1 1 - X 0 1 * X 1 0 = ℓ := hdet
  have hCH := cayley_hamilton_two X
  rw [hdet'] at hCH

  have hdiff : (X 0 0 + X 1 1 - t) • X = 0 := by
    have e1 : X * X = t • X - (ℓ : A) • 1 := by
      rw [← sub_eq_zero]; rw [← hMat]; abel
    have e2 : X * X = (X 0 0 + X 1 1) • X - (ℓ : A) • 1 := by
      rw [← sub_eq_zero]; rw [← hCH]; abel
    rw [sub_smul, sub_eq_zero]
    have := e2.symm.trans e1
    exact sub_left_injective this

  have hinv : X * LinearMap.toMatrix b b (ρA ι hι ρ hρ σ⁻¹) = 1 := by
    rw [hX, ← toMatrix_ρA ι hι b ρ hρ, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one b]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_apply, ρA_apply, Module.End.one_apply]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hsc : (X 0 0 + X 1 1 - t) • (1 : Matrix (Fin 2) (Fin 2) A) = 0 := by
    rw [← hinv, ← smul_mul_assoc, hdiff, zero_mul]
  have h00 := congrArg (fun Y : Matrix (Fin 2) (Fin 2) A => Y 0 0) hsc
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h00
  exact sub_eq_zero.mp h00

include hι hρ in

theorem engine [Module.Finite k A] :
    ∃ W : Submodule K ((K ⊗[k] V)), Module.finrank K W = 2 ∧
      ∃ hW : ∀ σ : G, ∀ x ∈ W, ρK (K := K) ρ σ x ∈ W,
        (∀ a : A, ∀ x ∈ W, (ι a).baseChange K x = Λ a • x) ∧
        ∀ (σ : G) (t : A) (ℓ : ℕ),
          (∀ v : V, ρ σ (ρ σ v) - ι t (ρ σ v) + (ℓ : k) • v = 0) →
          (b.repr (ρ σ (b 0)) 0 * b.repr (ρ σ (b 1)) 1
              - b.repr (ρ σ (b 1)) 0 * b.repr (ρ σ (b 0)) 1 = ℓ) →
          LinearMap.trace K W ((ρK (K := K) ρ σ).restrict (hW σ)) = Λ t := by
  haveI : Module.Finite K ((K ⊗[k] A)) := Module.Finite.base_change k K A
  have hker : RingHom.ker (ΛB (K := K) Λ : (K ⊗[k] A) →+* K) ≠ ⊤ := by
    intro h
    have h1 : (1 : (K ⊗[k] A)) ∈ RingHom.ker (ΛB (K := K) Λ : (K ⊗[k] A) →+* K) := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨a₀, ha₀0, ha₀'⟩ := exists_ann_of_ne_top K _ hker
  have ha₀ : ∀ m : (K ⊗[k] A), ΛB Λ m = 0 → m * a₀ = 0 := fun m hm => ha₀' m hm
  refine ⟨W ι b a₀, finrank_W ι hι b a₀ ha₀0, W_stable ι hι b Λ ρ hρ a₀ ha₀,
    W_hecke ι b Λ a₀ ha₀, fun σ t ℓ hES hdet => ?_⟩
  rw [trace_W ι hι b Λ ρ hρ a₀ ha₀ ha₀0, ← map_add, trace_M_eq ι hι b ρ hρ σ t ℓ hES hdet]

end Engine

section Transport

variable {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem stable_comap (Ψ : X ≃ₗ[K] Y) (W : Submodule K Y) (f : Module.End K X) (g : Module.End K Y)
    (hfg : ∀ x, Ψ (f x) = g (Ψ x)) (hW : ∀ w ∈ W, g w ∈ W) :
    ∀ w ∈ W.comap Ψ.toLinearMap, f w ∈ W.comap Ψ.toLinearMap := by
  intro w hw
  rw [Submodule.mem_comap, LinearEquiv.coe_coe, hfg]
  exact hW _ hw

def comapEquiv (Ψ : X ≃ₗ[K] Y) (W : Submodule K Y) : W.comap Ψ.toLinearMap ≃ₗ[K] W where
  toFun w := ⟨Ψ w, w.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)
  invFun y := ⟨Ψ.symm y, by
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; exact y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

theorem finrank_comap (Ψ : X ≃ₗ[K] Y) (W : Submodule K Y) :
    Module.finrank K (W.comap Ψ.toLinearMap) = Module.finrank K W :=
  LinearEquiv.finrank_eq (comapEquiv Ψ W)

theorem trace_restrict_comap (Ψ : X ≃ₗ[K] Y) (W : Submodule K Y) (f : Module.End K X)
    (g : Module.End K Y) (hfg : ∀ x, Ψ (f x) = g (Ψ x)) (hW : ∀ w ∈ W, g w ∈ W)
    (hW' : ∀ w ∈ W.comap Ψ.toLinearMap, f w ∈ W.comap Ψ.toLinearMap) :
    LinearMap.trace K (W.comap Ψ.toLinearMap) (f.restrict hW') =
      LinearMap.trace K W (g.restrict hW) := by
  have h : g.restrict hW = (comapEquiv Ψ W).conj (f.restrict hW') := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.coe_restrict_apply]
    show g y = Ψ (f (Ψ.symm y))
    rw [hfg, LinearEquiv.apply_symm_apply]
  rw [h, LinearMap.trace_conj']

theorem hecke_comap (Ψ : X ≃ₗ[K] Y) (W : Submodule K Y) (f : Module.End K X) (g : Module.End K Y)
    (hfg : ∀ x, Ψ (f x) = g (Ψ x)) (c : K) (hW : ∀ w ∈ W, g w = c • w) :
    ∀ w ∈ W.comap Ψ.toLinearMap, f w = c • w := by
  intro w hw
  apply Ψ.injective
  rw [hfg, map_smul]
  exact hW _ hw

theorem assemble (Ψ : X ≃ₗ[K] Y) {G : Type*} (fX : G → Module.End K X) (fY : G → Module.End K Y)
    (hf : ∀ σ x, Ψ (fX σ x) = fY σ (Ψ x))
    {I : Type*} (tX : I → Module.End K X) (tY : I → Module.End K Y)
    (ht : ∀ i x, Ψ (tX i x) = tY i (Ψ x)) (c : I → K) (P : G → I → Prop)
    (W₀ : Submodule K Y) (h2 : Module.finrank K W₀ = 2) (hst : ∀ σ, ∀ w ∈ W₀, fY σ w ∈ W₀)
    (hT : ∀ i, ∀ w ∈ W₀, tY i w = c i • w)
    (htr : ∀ σ i, P σ i → LinearMap.trace K W₀ ((fY σ).restrict (hst σ)) = c i) :
    ∃ W : Submodule K X, Module.finrank K W = 2 ∧ ∃ hW : ∀ σ, ∀ w ∈ W, fX σ w ∈ W,
      (∀ i, ∀ w ∈ W, tX i w = c i • w) ∧
      ∀ σ i, P σ i → LinearMap.trace K W ((fX σ).restrict (hW σ)) = c i := by
  refine ⟨W₀.comap Ψ.toLinearMap, (finrank_comap Ψ W₀).trans h2,
    fun σ => stable_comap Ψ W₀ _ _ (hf σ) (hst σ),
    fun i => hecke_comap Ψ W₀ _ _ (ht i) _ (hT i), fun σ i hP => ?_⟩
  rw [trace_restrict_comap Ψ W₀ _ _ (hf σ) (hst σ)]
  exact htr σ i hP

end Transport

section Coeff

theorem padicInt_injective (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] (f : ℤ_[p] →+* R) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hspec := PadicInt.unitCoeff_spec hne
  rw [hspec, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact ((PadicInt.unitCoeff hne).isUnit.map f).ne_zero h
  · have hp : (p : R) = 0 := pow_eq_zero_iff'.mp h |>.1
    exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.mp hp)

theorem exists_intermediateField {k F Ω : Type*} [Field k] [Field F] [Field Ω] [Algebra F Ω]
    [Algebra k F] [Algebra k Ω] [IsScalarTower k F Ω]
    {A : Type*} [CommRing A] [Algebra k A] [Module.Finite k A] (Λ : A →ₐ[k] Ω) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ ∀ a, Λ a ∈ L := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := k) (M := A)
  haveI : Algebra.IsIntegral k A := Algebra.IsIntegral.of_finite k A
  refine ⟨IntermediateField.adjoin F (Set.range (fun i => Λ (s i))), ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact ((Algebra.IsIntegral.isIntegral (R := k) (s i)).map Λ).tower_top
  · intro a
    have ha : a ∈ Submodule.span k (Set.range s) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply k F Ω]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hx

theorem coeff_package (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (F : Type*) [Field F] [Algebra 𝒪 F] [IsFractionRing 𝒪 F]
    (L : Type*) [Field L] [CharZero L] [Algebra 𝒪 L] [Algebra F L] [IsScalarTower 𝒪 F L]
    [FiniteDimensional F L] :
    Module.Finite 𝒪 (integralClosure 𝒪 L) ∧
    ∃ _ : IsDiscreteValuationRing (integralClosure 𝒪 L),
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure 𝒪 L)) (integralClosure 𝒪 L) ∧
      Finite (IsLocalRing.ResidueField (integralClosure 𝒪 L)) ∧
      IsLocalHom (algebraMap 𝒪 (integralClosure 𝒪 L)) ∧
      Function.Injective (algebraMap 𝒪 (integralClosure 𝒪 L)) ∧
      IsFractionRing (integralClosure 𝒪 L) L := by
  haveI : CharZero F := (algebraMap F L).charZero
  haveI : Algebra.IsSeparable F L := inferInstance
  obtain ⟨hfin, hdvr, hcpl⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪 F L
  haveI := hfin
  haveI := hdvr
  have hinj : Function.Injective (algebraMap 𝒪 (integralClosure 𝒪 L)) := by
    have h : Function.Injective (algebraMap 𝒪 L) := by
      rw [IsScalarTower.algebraMap_eq 𝒪 F L]
      exact (algebraMap F L).injective.comp (IsFractionRing.injective 𝒪 F)
    rw [IsScalarTower.algebraMap_eq 𝒪 (integralClosure 𝒪 L) L, RingHom.coe_comp] at h
    exact Function.Injective.of_comp h
  haveI : FaithfulSMul 𝒪 (integralClosure 𝒪 L) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 (integralClosure 𝒪 L)).mpr hinj
  haveI hloc : IsLocalHom (algebraMap 𝒪 (integralClosure 𝒪 L)) :=
    Algebra.IsIntegral.isLocalHom 𝒪 (integralClosure 𝒪 L)
  have hres : Finite (IsLocalRing.ResidueField (integralClosure 𝒪 L)) := by
    haveI := IsLocalRing.ResidueField.finite_of_module_finite (R := 𝒪) (S := integralClosure 𝒪 L)
    exact Module.finite_of_finite (IsLocalRing.ResidueField 𝒪)
  exact ⟨hfin, hdvr, hcpl, hres, hloc, hinj,
    IsIntegralClosure.isFractionRing_of_finite_extension 𝒪 F L (integralClosure 𝒪 L)⟩

end Coeff

section Jacobian

p2m_open "ModularCurve~baseChangeHom"

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

scoped instance isMulCommutative_rationalHeckeAlgebra : IsMulCommutative (rationalHeckeAlgebra p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingA : CommRing (rationalHeckeAlgebra p J) := inferInstance

theorem subalgebra_smul_def (a : rationalHeckeAlgebra p J) (v : RationalTateModule p J) :
    a • v = (a : Module.End ℚ_[p] (RationalTateModule p J)) v := rfl

theorem finite_rationalHeckeAlgebra [Module.Finite ℤ_[p] (_root_.TateModule p J)] :
    Module.Finite ℚ_[p] (rationalHeckeAlgebra p J) := by
  haveI : Module.Finite ℚ_[p] (RationalTateModule p J) :=
    Module.Finite.base_change ℤ_[p] ℚ_[p] (_root_.TateModule p J)
  exact Module.Finite.of_injective (rationalHeckeAlgebra p J).val.toLinearMap
    Subtype.val_injective

theorem mem_root_of_mem {x : ℕ → J} (hx : x ∈ ModularCurve.TateModule p J) :
    x ∈ _root_.TateModule p J := by
  change ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n
  intro n
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_smul_eq_nsmul ℤ]; exact ModularCurve.TateModule.pow_smul_apply hx n
  · rw [Nat.cast_smul_eq_nsmul ℤ]; exact hx.2 n

theorem mem_of_mem_root {x : ℕ → J} (hx : x ∈ _root_.TateModule p J) :
    x ∈ ModularCurve.TateModule p J := by
  change ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n at hx
  refine ⟨?_, fun n => ?_⟩
  · have h := (hx 0).1
    rwa [pow_zero, Nat.cast_one, one_smul] at h
  · have h := (hx n).2
    rwa [Nat.cast_smul_eq_nsmul ℤ] at h

theorem toZModPow_val (n : ℕ) (a : ℤ_[p]) : (PadicInt.toZModPow n a).val = a.appr n := by
  show (((a.appr n : ℕ) : ZMod (p ^ n))).val = a.appr n
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt a n)]

variable [Module ℤ_[p] (ModularCurve.TateModule p J)]
variable (hsmul : ∀ (a : ℤ_[p]) (x : ModularCurve.TateModule p J) (n : ℕ),
  ((a • x : ModularCurve.TateModule p J) : ℕ → J) n =
    (PadicInt.toZModPow n a).val • (x : ℕ → J) n)

def β : ModularCurve.TateModule p J ≃ₗ[ℤ_[p]] _root_.TateModule p J where
  toFun x := ⟨x, mem_root_of_mem p J x.2⟩
  invFun y := ⟨y, mem_of_mem_root p J y.2⟩
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    funext n
    show ((a • x : ModularCurve.TateModule p J) : ℕ → J) n =
      ((a.appr n : ℕ) : ℤ) • (x : ℕ → J) n
    rw [hsmul, toZModPow_val, Nat.cast_smul_eq_nsmul ℤ]
  left_inv _ := rfl
  right_inv _ := rfl

theorem β_hecke (t : HeckeAlg) (x : ModularCurve.TateModule p J) :
    β p J hsmul (t • x) = tateHeckeRep p J t (β p J hsmul x) :=
  Subtype.ext rfl

variable [DistribMulAction Gal J]

theorem β_galois (σ : Gal) (x : ModularCurve.TateModule p J) :
    β p J hsmul ⟨σ • (x : ℕ → J), ModularCurve.TateModule.smul_mem σ x.2⟩
      = _root_.TateModule.rep p J Gal σ (β p J hsmul x) :=
  Subtype.ext rfl

include hsmul in

theorem exists_bridge (O : Type) [CommRing O] [Algebra ℤ_[p] O]
    (K : Type) [Field K] [Algebra O K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] O K]
    [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (ρM : Gal →* Module.End O (O ⊗[ℤ_[p]] ModularCurve.TateModule p J))
    (hρ : ∀ (σ : Gal) (x y : ModularCurve.TateModule p J),
      (y : ℕ → J) = σ • (x : ℕ → J) → ∀ a : O, ρM σ (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] y)
    (TM : HeckeAlg →+* Module.End O (O ⊗[ℤ_[p]] ModularCurve.TateModule p J))
    (hT : ∀ (t : HeckeAlg) (a : O) (x : ModularCurve.TateModule p J),
      TM t (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] (t • x)) :
    ∃ Ψ : (K ⊗[O] (O ⊗[ℤ_[p]] ModularCurve.TateModule p J)) ≃ₗ[K]
        K ⊗[ℚ_[p]] RationalTateModule p J,
      (∀ (σ : Gal) (x : K ⊗[O] (O ⊗[ℤ_[p]] ModularCurve.TateModule p J)),
        Ψ ((ρM σ).baseChange K x) = (rationalGaloisRep p J Gal σ).baseChange K (Ψ x)) ∧
      (∀ (t : HeckeAlg) (x : K ⊗[O] (O ⊗[ℤ_[p]] ModularCurve.TateModule p J)),
        Ψ ((TM t).baseChange K x) = (rationalHeckeRep p J t).baseChange K (Ψ x)) := by
  let Ψ₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[p] O K K
    (ModularCurve.TateModule p J)
  let Ψ₂ := (β p J hsmul).baseChange ℤ_[p] K (ModularCurve.TateModule p J) (_root_.TateModule p J)
  let Ψ₃ := (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[p] ℚ_[p] K K
    (_root_.TateModule p J)).symm
  refine ⟨(Ψ₁.trans Ψ₂).trans Ψ₃, ?_, ?_⟩
  · intro σ v
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.tmul_zero]
      | tmul a x =>
        have hy := hρ σ x ⟨σ • (x : ℕ → J), ModularCurve.TateModule.smul_mem σ x.2⟩ rfl a
        simp only [LinearEquiv.trans_apply, LinearMap.baseChange_tmul, hy, Ψ₁, Ψ₂, Ψ₃,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearEquiv.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, β_galois,
          rationalGaloisRep_tmul]
      | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
    | add v w hv hw => simp only [map_add, hv, hw]
  · intro t v
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, TensorProduct.tmul_zero]
      | tmul a x =>
        simp only [LinearEquiv.trans_apply, LinearMap.baseChange_tmul, hT, Ψ₁, Ψ₂, Ψ₃,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearEquiv.baseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, β_hecke,
          rationalHeckeRep_tmul]
      | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
    | add v w hv hw => simp only [map_add, hv, hw]

omit [Module ℤ_[p] (ModularCurve.TateModule p J)] in

theorem commute_of_comm
    (hcomm : ∀ (σ : Gal) (t : HeckeAlg) (x : _root_.TateModule p J),
      _root_.TateModule.rep p J Gal σ (_root_.TateModule.rep p J HeckeAlg t x)
        = _root_.TateModule.rep p J HeckeAlg t (_root_.TateModule.rep p J Gal σ x))
    (σ : Gal) (a : rationalHeckeAlgebra p J) :
    (rationalHeckeAlgebra p J).val a * rationalGaloisRep p J Gal σ
      = rationalGaloisRep p J Gal σ * (rationalHeckeAlgebra p J).val a := by
  have hle : rationalHeckeAlgebra p J ≤
      Subalgebra.centralizer ℚ_[p] {rationalGaloisRep p J Gal σ} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro g rfl
    rw [rationalGaloisRep_apply, rationalHeckeRep_apply, ← LinearMap.baseChange_mul,
      ← LinearMap.baseChange_mul]
    exact congrArg _ (LinearMap.ext fun x => hcomm σ t x)
  have := (Subalgebra.mem_centralizer_iff ℚ_[p]).mp (hle a.2) _ rfl
  exact this.symm

omit [Module ℤ_[p] (ModularCurve.TateModule p J)] in

theorem es_rational {ℓ : ℕ} (hℓ : ℓ.Prime) (σ : Gal)
    (hES : ∀ x : _root_.TateModule p J,
      _root_.TateModule.rep p J Gal σ (_root_.TateModule.rep p J Gal σ x)
        - _root_.TateModule.rep p J HeckeAlg (heckeGen ⟨ℓ, hℓ⟩) (_root_.TateModule.rep p J Gal σ x)
        + ℓ • x = 0)
    (v : RationalTateModule p J) :
    rationalGaloisRep p J Gal σ (rationalGaloisRep p J Gal σ v)
      - rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩) (rationalGaloisRep p J Gal σ v)
      + (ℓ : ℚ_[p]) • v = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    rw [rationalGaloisRep_tmul, rationalGaloisRep_tmul, rationalHeckeRep_tmul,
      tateHeckeRep_apply, show ((ℓ : ℕ) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (ℓ : ℤ_[p]) from
        (map_natCast _ ℓ).symm, algebraMap_smul, ← TensorProduct.tmul_smul,
      Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_sub, ← TensorProduct.tmul_add, hES x,
      TensorProduct.tmul_zero]
  | add v w hv hw =>
    simp only [map_add, smul_add]
    calc _ = (rationalGaloisRep p J Gal σ (rationalGaloisRep p J Gal σ v)
            - rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩) (rationalGaloisRep p J Gal σ v)
            + (ℓ : ℚ_[p]) • v)
          + (rationalGaloisRep p J Gal σ (rationalGaloisRep p J Gal σ w)
            - rationalHeckeRep p J (heckeGen ⟨ℓ, hℓ⟩) (rationalGaloisRep p J Gal σ w)
            + (ℓ : ℚ_[p]) • w) := by
          abel
      _ = 0 := by rw [hv, hw, add_zero]

end Jacobian

section FinalPart

theorem core
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ) (hpS : p ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (C : Type) [CommRing C] [Algebra 𝒪' C] [Algebra ℤ_[p] C]
    (K : Type) [Field K] [Algebra C K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] C K]
    [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (ΛKa : letI := ModularCurve.heckeModuleBar N
      ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N) →ₐ[ℚ_[p]] K)
    (hΛK_T : letI := ModularCurve.heckeModuleBar N
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ΛKa ⟨ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩),
            ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra p (ModularCurve.JZero N) _⟩
          = algebraMap C K (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))) :
    letI := ModularCurve.heckeModuleBar N
    ∀ [Module ℤ_[p] (ModularCurve.TateModule p (ModularCurve.JZero N))]
      (_hsmul : ∀ (a : ℤ_[p]) (x : ModularCurve.TateModule p (ModularCurve.JZero N)) (n : ℕ),
        ((a • x : ModularCurve.TateModule p (ModularCurve.JZero N)) :
            ℕ → ModularCurve.JZero N) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → ModularCurve.JZero N) n)
      (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
        Module.End C (C ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N)))
      (_hρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x y : ModularCurve.TateModule p (ModularCurve.JZero N)),
        (y : ℕ → ModularCurve.JZero N) = σ • (x : ℕ → ModularCurve.JZero N) →
          ∀ a : C, ρM σ (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] y)
      (TM : ModularCurve.HeckeAlg →+*
        Module.End C (C ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N)))
      (_hT : ∀ (t : ModularCurve.HeckeAlg) (a : C)
        (x : ModularCurve.TateModule p (ModularCurve.JZero N)),
        TM t (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] (t • x)),
      ∃ W : Submodule K (K ⊗[C] (C ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N))),
        Module.finrank K W = 2 ∧
        ∃ hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
            (ρM σ).baseChange K w ∈ W,
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), ∀ w ∈ W,
            (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
              algebraMap C K (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) • w) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
              ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
                LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
                  algebraMap C K
                    (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))) := by
  letI := ModularCurve.heckeModuleBar N
  intro instT hsmul ρM hρ TM hT
  have hp : p.Prime := Fact.out
  have hcb := ModularCurve.heckeOperatorsCommuteBar N
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JZero N)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jZero N p
  haveI : Module.Finite ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) :=
    finite_rationalHeckeAlgebra p (ModularCurve.JZero N)

  have hΨ := exists_bridge p (ModularCurve.JZero N) hsmul C K ρM hρ TM hT
  obtain ⟨Ψ, hΨρ, hΨT⟩ := hΨ
  have hi : ModularCurve.RationalRankTwoCyclotomic N p :=
    ModularCurve.rationalRankTwoCyclotomic_family N p (Nat.pos_of_ne_zero (NeZero.ne N)) hp
  obtain ⟨b, hb⟩ := hi
  have hcomm := commute_of_comm p (ModularCurve.JZero N)
    (fun σ t x => ModularCurve.rep_tateModule_jZero_comm N p hcb σ t x)
  have hgood : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N * p := by
    intro ℓ hℓ hℓN hℓS h
    have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ Finset.mem_coe.mpr hpS)
    exact ((Nat.Prime.dvd_mul hℓ).mp h).elim hℓN fun h' =>
      hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h')

  have hE :=
    engine (K := K) (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)).val
      (fun a v => rfl) b ΛKa
      (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
        (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) hcomm
  obtain ⟨W₀, hW₀2, hW₀st, hW₀T, hW₀tr⟩ := hE

  have htr : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ (↑S : Set ℕ)}),
      (∃ A' : ValuationSubring (AlgebraicClosure ℚ), A'.LiesOverPrime i.1 ∧ A'.IsFrobeniusAt σ i.1) →
        LinearMap.trace K W₀ ((ρK (K := K) (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) σ).restrict (hW₀st σ)) =
          algebraMap C K (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T i.2.1 i.2.2.1 i.2.2.2))) := by
    rintro σ ⟨ℓ, hℓ, hℓN, hℓS⟩ ⟨A', hA', hσ⟩
    rw [← hΛK_T ℓ hℓ hℓN hℓS]
    exact hW₀tr σ _ ℓ
      (es_rational p (ModularCurve.JZero N) hℓ σ fun x =>
        ModularCurve.frobeniusQuadratic_tateModule_jZero N p hcb hℓ (hgood ℓ hℓ hℓN hℓS)
          A' hA' σ hσ x)
      (hb ℓ hℓ (hgood ℓ hℓ hℓN hℓS) A' hA' σ hσ)
  have hTT : ∀ (i : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ (↑S : Set ℕ)}), ∀ w ∈ W₀,
      (ModularCurve.rationalHeckeRep p (ModularCurve.JZero N)
        (ModularCurve.heckeGen ⟨i.1, i.2.1⟩)).baseChange K w =
      algebraMap C K (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T i.2.1 i.2.2.1 i.2.2.2))) • w := by
    rintro ⟨ℓ, hℓ, hℓN, hℓS⟩ w hw
    rw [← hΛK_T ℓ hℓ hℓN hℓS]
    exact hW₀T ⟨_, ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra p _ _⟩ w hw

  have hA := assemble Ψ
    (fun σ => (ρM σ).baseChange K)
    (fun σ => (ModularCurve.rationalGaloisRep p (ModularCurve.JZero N)
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K)
    hΨρ
    (I := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ (↑S : Set ℕ)})
    (fun i => (TM (ModularCurve.heckeGen ⟨i.1, i.2.1⟩)).baseChange K)
    (fun i => (ModularCurve.rationalHeckeRep p (ModularCurve.JZero N)
      (ModularCurve.heckeGen ⟨i.1, i.2.1⟩)).baseChange K)
    (fun i => hΨT _)
    (fun i => algebraMap C K (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T i.2.1 i.2.2.1 i.2.2.2))))
    (fun σ i => ∃ A' : ValuationSubring (AlgebraicClosure ℚ),
      A'.LiesOverPrime i.1 ∧ A'.IsFrobeniusAt σ i.1)
    W₀ hW₀2 hW₀st hTT htr
  obtain ⟨W, hW2, hW, hWT, hWtr⟩ := hA
  exact ⟨W, hW2, hW, fun ℓ hℓ hℓN hℓS => hWT ⟨ℓ, hℓ, hℓN, hℓS⟩,
    fun ℓ hℓ hℓN hℓS A' hA' σ hσ => hWtr σ ⟨ℓ, hℓ, hℓN, hℓS⟩ ⟨A', hA', hσ⟩⟩

theorem forall_fractionRing
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ) (hpS : p ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (C : Type) [CommRing C] [IsDomain C] [CharZero C] [Algebra 𝒪' C] [Algebra ℤ_[p] C]
    (L : Type) [Field L] [Algebra C L] [IsFractionRing C L]
    (ΛL : letI := ModularCurve.heckeModuleBar N
      ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N) →+* L)
    (hP1 : letI := ModularCurve.heckeModuleBar N
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ΛL ⟨ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩),
            ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra p (ModularCurve.JZero N) _⟩
          = algebraMap C L (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))))
    (hP2 : letI := ModularCurve.heckeModuleBar N
      ∀ c : ℤ_[p],
        ΛL (algebraMap ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))
            (algebraMap ℤ_[p] ℚ_[p] c))
          = algebraMap C L (algebraMap ℤ_[p] C c)) :
    ∀ (K : Type) [Field K] [Algebra C K] [IsFractionRing C K],
    letI := ModularCurve.heckeModuleBar N
    ∀ [Module ℤ_[p] (ModularCurve.TateModule p (ModularCurve.JZero N))]
      (_hsmul : ∀ (a : ℤ_[p]) (x : ModularCurve.TateModule p (ModularCurve.JZero N)) (n : ℕ),
        ((a • x : ModularCurve.TateModule p (ModularCurve.JZero N)) :
            ℕ → ModularCurve.JZero N) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → ModularCurve.JZero N) n)
      (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
        Module.End C (C ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N)))
      (_hρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x y : ModularCurve.TateModule p (ModularCurve.JZero N)),
        (y : ℕ → ModularCurve.JZero N) = σ • (x : ℕ → ModularCurve.JZero N) →
          ∀ a : C, ρM σ (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] y)
      (TM : ModularCurve.HeckeAlg →+*
        Module.End C (C ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N)))
      (_hT : ∀ (t : ModularCurve.HeckeAlg) (a : C)
        (x : ModularCurve.TateModule p (ModularCurve.JZero N)),
        TM t (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] (t • x)),
      ∃ W : Submodule K (K ⊗[C] (C ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N))),
        Module.finrank K W = 2 ∧
        ∃ hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
            (ρM σ).baseChange K w ∈ W,
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), ∀ w ∈ W,
            (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
              algebraMap C K (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) • w) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
              ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
                LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
                  algebraMap C K
                    (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))) := by
  intro K _ _ _
  letI := ModularCurve.heckeModuleBar N

  letI algZK : Algebra ℤ_[p] K := ((algebraMap C K).comp (algebraMap ℤ_[p] C)).toAlgebra
  haveI : IsScalarTower ℤ_[p] C K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective C K)
  have hinjZK : Function.Injective (algebraMap ℤ_[p] K) := padicInt_injective p _
  letI algQK : Algebra ℚ_[p] K := (IsFractionRing.lift hinjZK : ℚ_[p] →+* K).toAlgebra
  haveI : IsScalarTower ℤ_[p] ℚ_[p] K :=
    IsScalarTower.of_algebraMap_eq (fun c => (IsFractionRing.lift_algebraMap hinjZK c).symm)

  let eK : L ≃ₐ[C] K := IsLocalization.algEquiv (nonZeroDivisors C) L K
  let ΛK : ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N) →+* K :=
    (eK : L →+* K).comp ΛL
  have hΛK_T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ΛK ⟨ModularCurve.rationalHeckeRep p (ModularCurve.JZero N) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩),
          ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra p (ModularCurve.JZero N) _⟩
        = algebraMap C K (algebraMap 𝒪' C (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) := by
    intro ℓ hℓ hℓN hℓS
    show eK (ΛL _) = _
    rw [hP1, AlgEquiv.commutes]
  have hΛK_Z : ∀ c : ℤ_[p],
      ΛK (algebraMap ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))
          (algebraMap ℤ_[p] ℚ_[p] c))
        = algebraMap ℤ_[p] K c := by
    intro c
    show eK (ΛL _) = _
    rw [hP2, AlgEquiv.commutes]
    rfl
  have hΛK_Q : ∀ q : ℚ_[p],
      ΛK (algebraMap ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) q)
        = algebraMap ℚ_[p] K q := by
    have h := IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
      (j := ΛK.comp (algebraMap ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))))
      (k := algebraMap ℚ_[p] K) (RingHom.ext fun c => by
        show ΛK (algebraMap ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))
          (algebraMap ℤ_[p] ℚ_[p] c)) = algebraMap ℚ_[p] K (algebraMap ℤ_[p] ℚ_[p] c)
        rw [hΛK_Z c]
        exact IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K c)
    intro q
    exact congrArg (fun f => f q) h
  intro instT hsmul ρM hρ TM hT
  exact core p N S hpS 𝒪' χ C K { toRingHom := ΛK, commutes' := hΛK_Q } hΛK_T hsmul ρM hρ TM hT

end FinalPart

end EigenPlaneOfPoint
p2m_reactivate "P2MW.S_CuspForm_exists_eigenPlane_tateModule_jZero_of_point.EigenPlaneOfPoint"

open EigenPlaneOfPoint in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ) (_hpS : p ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')]
    [CharZero 𝒪'] (_hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪') :
    ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪'') 𝒪'')
      (_ : Finite (IsLocalRing.ResidueField 𝒪'')) (_ : CharZero 𝒪'')
      (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'') (_ : IsLocalHom (algebraMap 𝒪' 𝒪''))
      (_ : Algebra ℤ_[p] 𝒪''),
    Function.Injective (algebraMap 𝒪' 𝒪'') ∧
    ∀ (K : Type) [Field K] [Algebra 𝒪'' K] [IsFractionRing 𝒪'' K],
    letI := ModularCurve.heckeModuleBar N
    ∀ [Module ℤ_[p] (ModularCurve.TateModule p (ModularCurve.JZero N))]
      (_hsmul : ∀ (a : ℤ_[p]) (x : ModularCurve.TateModule p (ModularCurve.JZero N)) (n : ℕ),
        ((a • x : ModularCurve.TateModule p (ModularCurve.JZero N)) :
            ℕ → ModularCurve.JZero N) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → ModularCurve.JZero N) n)
      (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
        Module.End 𝒪'' (𝒪'' ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N)))
      (_hρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x y : ModularCurve.TateModule p (ModularCurve.JZero N)),
        (y : ℕ → ModularCurve.JZero N) = σ • (x : ℕ → ModularCurve.JZero N) →
          ∀ a : 𝒪'', ρM σ (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] y)
      (TM : ModularCurve.HeckeAlg →+*
        Module.End 𝒪'' (𝒪'' ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N)))
      (_hT : ∀ (t : ModularCurve.HeckeAlg) (a : 𝒪'')
        (x : ModularCurve.TateModule p (ModularCurve.JZero N)),
        TM t (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] (t • x)),
      ∃ W : Submodule K (K ⊗[𝒪''] (𝒪'' ⊗[ℤ_[p]] ModularCurve.TateModule p (ModularCurve.JZero N))),
        Module.finrank K W = 2 ∧
        ∃ hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
            (ρM σ).baseChange K w ∈ W,
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), ∀ w ∈ W,
            (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
              algebraMap 𝒪'' K (algebraMap 𝒪' 𝒪'' (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) • w) ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
            ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
              ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
                LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
                  algebraMap 𝒪'' K
                    (algebraMap 𝒪' 𝒪'' (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)))) := by

  letI := ModularCurve.heckeModuleBar N
  have hcb := ModularCurve.heckeOperatorsCommuteBar N
  have hin := ModularCurve.heckeInputsAll N
  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JZero N)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jZero N p
  haveI : Module.Finite ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) :=
    finite_rationalHeckeAlgebra p (ModularCurve.JZero N)

  let i₀ : ℤ_[p] →+* 𝒪' := GaloisRep.padicIntToRing 𝒪' p _hp𝒪'
  have hi₀ : Function.Injective ((algebraMap 𝒪' (FractionRing 𝒪')).comp i₀) :=
    padicInt_injective p _
  let jF : ℚ_[p] →+* FractionRing 𝒪' := IsFractionRing.lift hi₀
  letI algQF : Algebra ℚ_[p] (FractionRing 𝒪') := jF.toAlgebra
  haveI : CharZero (FractionRing 𝒪') :=
    charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪' (FractionRing 𝒪'))

  have hexΛ :=
    ModularCurve.exists_ringHom_rationalHeckeAlgebra_extends_heckeChar N p hin hcb (↑S : Set ℕ)
      (AlgebraicClosure (FractionRing 𝒪'))
      ((algebraMap (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪'))).comp
        ((algebraMap 𝒪' (FractionRing 𝒪')).comp χ))
  let Λ : ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N) →+*
      AlgebraicClosure (FractionRing 𝒪') := hexΛ.choose
  have hΛc : ∀ c : ℚ_[p],
      Λ (algebraMap ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) c)
        = algebraMap ℚ_[p] (AlgebraicClosure (FractionRing 𝒪')) c := hexΛ.choose_spec.1
  have hΛT := hexΛ.choose_spec.2
  let Λa : ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N) →ₐ[ℚ_[p]]
      AlgebraicClosure (FractionRing 𝒪') :=
    { toRingHom := Λ, commutes' := hΛc }
  have hexL := exists_intermediateField (F := FractionRing 𝒪') Λa
  let L : IntermediateField (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪')) := hexL.choose
  haveI hLfd : FiniteDimensional (FractionRing 𝒪') L := hexL.choose_spec.1
  have hΛL : ∀ a, Λ a ∈ L := hexL.choose_spec.2
  haveI : CharZero L := (algebraMap L (AlgebraicClosure (FractionRing 𝒪'))).charZero

  have hpk := coeff_package 𝒪' (FractionRing 𝒪') L
  have hfin := hpk.1
  have hdvr : IsDiscreteValuationRing (integralClosure 𝒪' L) := hpk.2.choose
  have hcpl := hpk.2.choose_spec.1
  have hres := hpk.2.choose_spec.2.1
  have hloc := hpk.2.choose_spec.2.2.1
  have hinj := hpk.2.choose_spec.2.2.2.1
  haveI hfrac : IsFractionRing (integralClosure 𝒪' L) L := hpk.2.choose_spec.2.2.2.2
  haveI hcz : CharZero (integralClosure 𝒪' L) := (algebraMap (integralClosure 𝒪' L) L).charZero
  letI algZC : Algebra ℤ_[p] (integralClosure 𝒪' L) :=
    ((algebraMap 𝒪' (integralClosure 𝒪' L)).comp i₀).toAlgebra

  have hΛval : ∀ (a : ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) (z : 𝒪'),
      Λ a = algebraMap (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪'))
        (algebraMap 𝒪' (FractionRing 𝒪') z) →
      Λ.codRestrict L hΛL a = algebraMap (integralClosure 𝒪' L) L
        (algebraMap 𝒪' (integralClosure 𝒪' L) z) := by
    intro a z hz
    apply Subtype.ext
    rw [← IsScalarTower.algebraMap_apply 𝒪' (integralClosure 𝒪' L) L]
    show Λ a = ((algebraMap 𝒪' L z : L) : AlgebraicClosure (FractionRing 𝒪'))
    rw [hz, ← IsScalarTower.algebraMap_apply]
    rfl
  have hP1 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      Λ.codRestrict L hΛL ⟨ModularCurve.rationalHeckeRep p (ModularCurve.JZero N)
          (ModularCurve.heckeGen ⟨ℓ, hℓ⟩),
          ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra p (ModularCurve.JZero N) _⟩
        = algebraMap (integralClosure 𝒪' L) L
          (algebraMap 𝒪' (integralClosure 𝒪' L) (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) :=
    fun ℓ hℓ hℓN hℓS => hΛval _ _ (hΛT ℓ hℓ hℓN hℓS)
  have hP2 : ∀ c : ℤ_[p],
      Λ.codRestrict L hΛL
          (algebraMap ℚ_[p] (ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N))
            (algebraMap ℤ_[p] ℚ_[p] c))
        = algebraMap (integralClosure 𝒪' L) L (algebraMap ℤ_[p] (integralClosure 𝒪' L) c) := by
    intro c
    refine hΛval _ (i₀ c) ?_
    rw [hΛc, IsScalarTower.algebraMap_apply ℚ_[p] (FractionRing 𝒪')
      (AlgebraicClosure (FractionRing 𝒪'))]
    show algebraMap (FractionRing 𝒪') _ (jF (algebraMap ℤ_[p] ℚ_[p] c)) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  exact ⟨integralClosure 𝒪' L, inferInstance, inferInstance, hdvr, hcpl, hres, hcz, inferInstance,
    hfin, hloc, algZC, hinj,
    forall_fractionRing p N S _hpS 𝒪' χ (integralClosure 𝒪' L) L (Λ.codRestrict L hΛL) hP1 hP2⟩

end
end S_CuspForm_exists_eigenPlane_tateModule_jZero_of_point
end P2MW
export P2MW.S_CuspForm_exists_eigenPlane_tateModule_jZero_of_point (solution)

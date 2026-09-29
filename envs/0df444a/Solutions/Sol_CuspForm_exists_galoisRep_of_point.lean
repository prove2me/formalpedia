-- Prove2me | solution 1 for CuspForm.exists_galoisRep_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e3ee52eb-f702-5213-8b89-e83d620a00ee

import Mathlib
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Theorems.Thm_ModularCurve_exists_ringHom_rationalHeckeAlgebra_extends_heckeChar
import Theorems.Thm_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar
import Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_galoisRep_of_point
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

open Polynomial

noncomputable section

namespace W6BPP

theorem padicIntToRing_injective (p : ℕ) [Fact p.Prime] (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    Function.Injective (GaloisRep.padicIntToRing 𝒪 p hp) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hne
  have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (GaloisRep.padicIntToRing 𝒪 p hp) := by
    rw [hn]; exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_ne_zero n (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hmem

theorem coefficientRing (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (L' : Type) [Field L'] [Algebra 𝒪 L'] [Algebra (FractionRing 𝒪) L']
    [IsScalarTower 𝒪 (FractionRing 𝒪) L'] [FiniteDimensional (FractionRing 𝒪) L'] :
    ∃ (_ : IsDiscreteValuationRing ↥(integralClosure 𝒪 L')),
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(integralClosure 𝒪 L')) ↥(integralClosure 𝒪 L') ∧
      Finite (IsLocalRing.ResidueField ↥(integralClosure 𝒪 L')) ∧
      CharZero ↥(integralClosure 𝒪 L') ∧
      Module.Finite 𝒪 ↥(integralClosure 𝒪 L') ∧
      IsLocalHom (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) ∧
      Function.Injective (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) ∧
      IsFractionRing ↥(integralClosure 𝒪 L') L' := by
  haveI : Algebra.IsSeparable (FractionRing 𝒪) L' := inferInstance
  obtain ⟨hfin, hdvr, hcomp⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪
      (FractionRing 𝒪) L'
  haveI := hfin
  haveI := hdvr

  have hinjL : Function.Injective (algebraMap 𝒪 L') := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (FractionRing 𝒪) L']
    exact (algebraMap (FractionRing 𝒪) L').injective.comp (IsFractionRing.injective 𝒪 _)
  have hinj : Function.Injective (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) := fun x y h =>
    hinjL (by
      have h' := congrArg (fun z : ↥(integralClosure 𝒪 L') => (z : L')) h
      simpa only [Subalgebra.coe_algebraMap] using h')
  haveI : FaithfulSMul 𝒪 ↥(integralClosure 𝒪 L') :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 _).2 hinj
  have hloc : IsLocalHom (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) :=
    Algebra.IsIntegral.isLocalHom 𝒪 _
  haveI := hloc
  have hres : Finite (IsLocalRing.ResidueField ↥(integralClosure 𝒪 L')) :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) inferInstance
  haveI : CharZero L' :=
    (RingHom.charZero_iff (algebraMap (FractionRing 𝒪) L').injective).1 inferInstance
  have hcz : CharZero ↥(integralClosure 𝒪 L') := (algebraMap ↥(integralClosure 𝒪 L') L').charZero
  have hfrac : IsFractionRing ↥(integralClosure 𝒪 L') L' :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing 𝒪) L'
  exact ⟨hdvr, hcomp, hres, hcz, hfin, hloc, hinj, hfrac⟩

section Instances

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlg J]

scoped instance isMulCommutative_A : IsMulCommutative (ModularCurve.rationalHeckeAlgebra p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingA : CommRing (ModularCurve.rationalHeckeAlgebra p J) := inferInstance

end Instances

theorem main
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ)
      (hpS : p ∈ S) (_hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
      (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
      [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')]
      [CharZero 𝒪'] (hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
      (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪') :
      ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪'') 𝒪'')
        (_ : Finite (IsLocalRing.ResidueField 𝒪'')) (_ : CharZero 𝒪'')
        (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'') (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
      Function.Injective (algebraMap 𝒪' 𝒪'') ∧
      ∃ ρ : GaloisRepAdic 𝒪'',
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap 𝒪' 𝒪'' (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) * X
                  + C ((ℓ : 𝒪''))) ∧
        (∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρ.IsUnramifiedAt q) := by
  letI := ModularCurve.heckeModuleBar N
  have hin : ModularCurve.HeckeInputsAll N := ModularCurve.heckeInputsAll N
  have hcomm : ModularCurve.HeckeOperatorsCommuteBar N := ModularCurve.heckeOperatorsCommuteBar N

  set i𝒪 : ℤ_[p] →+* 𝒪' := GaloisRep.padicIntToRing 𝒪' p hp𝒪' with hi𝒪
  have hi_inj : Function.Injective i𝒪 := W6BPP.padicIntToRing_injective p 𝒪' hp𝒪'
  have hg_inj : Function.Injective ((algebraMap 𝒪' (FractionRing 𝒪')).comp i𝒪) :=
    (IsFractionRing.injective 𝒪' (FractionRing 𝒪')).comp hi_inj
  set jL : ℚ_[p] →+* FractionRing 𝒪' := IsFractionRing.lift hg_inj with hjL
  have hjL : ∀ c : ℤ_[p], jL (c : ℚ_[p]) = algebraMap 𝒪' (FractionRing 𝒪') (i𝒪 c) := fun c => by
    rw [← PadicInt.algebraMap_apply, hjL, IsFractionRing.lift_algebraMap]
    rfl
  letI : Algebra ℚ_[p] (AlgebraicClosure (FractionRing 𝒪')) :=
    ((algebraMap (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪'))).comp jL).toAlgebra
  have halg : ∀ c : ℚ_[p], algebraMap ℚ_[p] (AlgebraicClosure (FractionRing 𝒪')) c
      = algebraMap (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪')) (jL c) := fun _ => rfl

  obtain ⟨Λ, hc, hT⟩ := ModularCurve.exists_ringHom_rationalHeckeAlgebra_extends_heckeChar N p hin hcomm
    (↑S : Set ℕ) (AlgebraicClosure (FractionRing 𝒪'))
    ((algebraMap 𝒪' (AlgebraicClosure (FractionRing 𝒪'))).comp χ)

  haveI : Module.Finite ℤ_[p] (TateModule p (ModularCurve.JZero N)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jZero N p
  haveI : Module.Finite ℚ_[p] (ModularCurve.RationalTateModule p (ModularCurve.JZero N)) :=
    inferInstance
  haveI : Module.Finite ℚ_[p]
      (Module.End ℚ_[p] (ModularCurve.RationalTateModule p (ModularCurve.JZero N))) := inferInstance
  haveI : Module.Finite ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) :=
    Module.Finite.of_injective (Subalgebra.val _).toLinearMap Subtype.val_injective
  obtain ⟨L', hL'⟩ : ∃ L' : IntermediateField (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪')),
      L' = IntermediateField.adjoin (FractionRing 𝒪') (Set.range Λ) := ⟨_, rfl⟩
  haveI : FiniteDimensional (FractionRing 𝒪') ↥L' := by
    rw [hL']
    exact RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range (R := ℚ_[p]) Λ
      (fun r => ⟨jL r, by rw [hc r, halg]⟩)
  have hΛmem : ∀ x, Λ x ∈ L' := fun x => by
    rw [hL']
    exact IntermediateField.subset_adjoin (FractionRing 𝒪') _ (Set.mem_range_self x)

  obtain ⟨hdvr, hcomp, hres, hcz, hfin, hloc, hinj, hfrac⟩ := W6BPP.coefficientRing 𝒪' ↥L'
  haveI := hdvr
  haveI := hfrac
  haveI := hloc
  have hp'' : (p : ↥(integralClosure 𝒪' ↥L')) ∈
      IsLocalRing.maximalIdeal ↥(integralClosure 𝒪' ↥L') := by
    rw [IsLocalRing.mem_maximalIdeal, ← map_natCast (algebraMap 𝒪' ↥(integralClosure 𝒪' ↥L')) p,
      map_mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact hp𝒪'

  let Λ' : ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) →+* ↥L' :=
    { toFun := fun x => ⟨Λ x, hΛmem x⟩
      map_one' := Subtype.ext (map_one Λ)
      map_mul' := fun x y => Subtype.ext (map_mul Λ x y)
      map_zero' := Subtype.ext (map_zero Λ)
      map_add' := fun x y => Subtype.ext (map_add Λ x y) }
  have hΛ'val : ∀ x, ((Λ' x : ↥L') : AlgebraicClosure (FractionRing 𝒪')) = Λ x := fun _ => rfl
  have hcoe𝒪 : ∀ y : 𝒪',
      ((algebraMap ↥(integralClosure 𝒪' ↥L') ↥L' (algebraMap 𝒪' ↥(integralClosure 𝒪' ↥L') y) : ↥L') :
        AlgebraicClosure (FractionRing 𝒪'))
        = algebraMap (FractionRing 𝒪') (AlgebraicClosure (FractionRing 𝒪'))
            (algebraMap 𝒪' (FractionRing 𝒪') y) := fun y => by
    rw [← IsScalarTower.algebraMap_apply 𝒪' ↥(integralClosure 𝒪' ↥L') ↥L']
    change algebraMap 𝒪' (AlgebraicClosure (FractionRing 𝒪')) y = _
    exact IsScalarTower.algebraMap_apply 𝒪' (FractionRing 𝒪') _ y
  have hΛ'c : ∀ c : ℤ_[p],
      Λ' (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebra p (ModularCurve.JZero N)) (c : ℚ_[p]))
        = algebraMap ↥(integralClosure 𝒪' ↥L') ↥L'
            (((algebraMap 𝒪' ↥(integralClosure 𝒪' ↥L')).comp i𝒪) c) := fun c => by
    apply Subtype.ext
    rw [hΛ'val, hc, halg, hjL, RingHom.comp_apply, hcoe𝒪]

  have E1 := ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeChar N p
    ↥(integralClosure 𝒪' ↥L') ↥L' ((algebraMap 𝒪' ↥(integralClosure 𝒪' ↥L')).comp i𝒪) hp''
  have E2 := E1 Λ' hΛ'c
  obtain ⟨ρ, hchar, hunr⟩ := E2

  have hp : p.Prime := Fact.out
  have hNp : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ¬ ℓ ∣ N * p := fun ℓ hℓ hℓN hℓp h =>
    (hℓ.dvd_mul.1 h).elim hℓN (fun h' => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h'))
  refine ⟨↥(integralClosure 𝒪' ↥L'), inferInstance, inferInstance, hdvr, hcomp, hres, hcz,
    inferInstance, hfin, hloc, hinj, ρ, ?_, fun q hq hqN hqp => hunr q hq (hNp q hq hqN hqp)⟩
  intro ℓ hℓ hℓN hℓS A hA σ hσ
  have hℓp : ℓ ≠ p := fun h => hℓS (by rw [h]; exact Finset.mem_coe.2 hpS)
  refine hchar ℓ hℓ (hNp ℓ hℓ hℓN hℓp) _ ?_ A hA σ hσ
  apply Subtype.ext
  rw [hΛ'val, hT ℓ hℓ hℓN hℓS, RingHom.comp_apply, hcoe𝒪]
  exact IsScalarTower.algebraMap_apply 𝒪' (FractionRing 𝒪') _ _

end W6BPP

theorem solution :
    ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ)
      (_hpS : p ∈ S) (_hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
      (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
      [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪') 𝒪'] [Finite (IsLocalRing.ResidueField 𝒪')]
      [CharZero 𝒪'] (_hp𝒪' : (p : 𝒪') ∈ IsLocalRing.maximalIdeal 𝒪')
      (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪'),
      ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪'') 𝒪'')
        (_ : Finite (IsLocalRing.ResidueField 𝒪'')) (_ : CharZero 𝒪'')
        (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'') (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
      Function.Injective (algebraMap 𝒪' 𝒪'') ∧
      ∃ ρ : GaloisRepAdic 𝒪'',
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap 𝒪' 𝒪'' (χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) * X
                  + C ((ℓ : 𝒪''))) ∧
        (∀ q : ℕ, q.Prime → ¬ q ∣ N → q ≠ p → ρ.IsUnramifiedAt q) := by
  intro p _ N _ S hpS hNS 𝒪' _ _ _ _ _ _ hp𝒪' χ
  exact W6BPP.main p N S hpS hNS 𝒪' hp𝒪' χ

end
end S_CuspForm_exists_galoisRep_of_point
end P2MW
export P2MW.S_CuspForm_exists_galoisRep_of_point (solution)

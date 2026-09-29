-- Prove2me | solution 1 for CohCarrier.exists_ideal_forall_heckeAlg_baseChange_eq_smul_of_exists_jZero_pTorsion_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3874a0a1-1fef-5cf7-afbe-8dadc8d94724

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_exists_not_dvd_and_smul_mem_heckeAlgebra_of_finite
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_ModularCurve_exists_ringHom_heckeAlgebra_heckeOperatorBar
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_JZero_cardinalityAJ_genusFF
import Theorems.Thm_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_ideal_forall_heckeAlg_baseChange_eq_smul_of_exists_jZero_pTorsion_eigenvector
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient"
p2m_attr_erase "instance" "FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsElliptic_tateBase ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

open ModularCurve
open scoped TensorProduct

namespace SolAN

theorem finite_heckeTorsion (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (𝔪 : Ideal HeckeAlg)
    (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪) :
    letI := heckeModuleBar M
    Finite ↥(heckeTorsion (JZero M) 𝔪) := by
  letI := heckeModuleBar M
  have hfin := JZero.finite_torsion_pow_of_cardinalityAJ M p (JZero.cardinalityAJ_genusFF M p) 1
  rw [pow_one] at hfin
  let f : ↥(heckeTorsion (JZero M) 𝔪) →
      ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M) p) :=
    fun x => ⟨(x : JZero M), by
      rw [AlgebraicCurve.Pic0.mem_torsion]
      have hx := (mem_heckeTorsion_iff (JZero M) 𝔪 x).mp x.2 _ hp𝔪
      have hC : ((p : ℕ) : HeckeAlg) = MvPolynomial.C (p : ℤ) := by simp
      rw [hC, heckeModuleBar_C_smul] at hx
      exact hx⟩
  exact Finite.of_injective f fun x y h => Subtype.ext (congrArg Subtype.val h :)

end SolAN

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
open ModularCurve in
open scoped TensorProduct in
theorem solution
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (M' : ℕ) [NeZero M'] (hpM : ¬ p ∣ M') (S : Finset ℕ)
    (θbar : CohCarrier.Gen M' ↑S → k)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) :
    letI := heckeModuleBar M'

    let Jp := ↥(heckeTorsion (JZero M') (Ideal.span {((p : ℕ) : HeckeAlg)}))
    let op : HeckeAlg → (k ⊗[ℤ] Jp →ₗ[k] k ⊗[ℤ] Jp) :=
      fun t => (DistribSMul.toLinearMap ℤ Jp t).baseChange k

    (∃ w : k ⊗[ℤ] Jp, w ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
        op (heckeGen ⟨ℓ, hℓ⟩) w = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) • w) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M'),
        op (heckeGen ⟨q, hq⟩) w = θbar (CohCarrier.Gen.U q hq hqM) • w) ∧
      (∀ d : (ZMod M')ˣ, w = θbar (CohCarrier.Gen.dia d) • w)) →

    ∃ (𝔪 : Ideal HeckeAlg) (_ : 𝔪.IsMaximal) (ι : HeckeAlg ⧸ 𝔪 →+* k),
      ((p : ℕ) : HeckeAlg) ∈ 𝔪 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
        ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M'),
        ι (Ideal.Quotient.mk 𝔪 (heckeGen ⟨q, hq⟩)) = θbar (CohCarrier.Gen.U q hq hqM)) ∧
      ∀ (t : HeckeAlg) (w : k ⊗[ℤ] Jp),
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
          op (heckeGen ⟨ℓ, hℓ⟩) w = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) • w) →
        (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M'),
          op (heckeGen ⟨q, hq⟩) w = θbar (CohCarrier.Gen.U q hq hqM) • w) →
        (∀ d : (ZMod M')ˣ, w = θbar (CohCarrier.Gen.dia d) • w) →
        op t w = ι (Ideal.Quotient.mk 𝔪 t) • w := by
  intro Jp op hW
  classical
  letI := heckeModuleBar M'
  have hcomm : HeckeOperatorsCommuteBar M' := heckeOperatorsCommuteBar M'

  let PE : k ⊗[ℤ] Jp → Prop := fun w =>
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
        op (heckeGen ⟨ℓ, hℓ⟩) w = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) • w) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M'),
        op (heckeGen ⟨q, hq⟩) w = θbar (CohCarrier.Gen.U q hq hqM) • w)
  obtain ⟨w₀, hw₀, hw₀T, hw₀U, -⟩ := hW
  have hPE₀ : PE w₀ := ⟨hw₀T, hw₀U⟩

  have hop_def : ∀ t, op t = (DistribSMul.toLinearMap ℤ Jp t).baseChange k := fun t => rfl
  have hop_mul : ∀ s t : HeckeAlg, op (s * t) = op s ∘ₗ op t := by
    intro s t
    rw [hop_def, hop_def, hop_def, ← LinearMap.baseChange_comp]
    congr 1
    apply LinearMap.ext
    intro x
    simp only [DistribSMul.toLinearMap_apply, LinearMap.comp_apply, mul_smul]
  have hop_add : ∀ s t : HeckeAlg, op (s + t) = op s + op t := by
    intro s t
    rw [hop_def, hop_def, hop_def, ← LinearMap.baseChange_add]
    congr 1
    apply LinearMap.ext
    intro x
    simp only [DistribSMul.toLinearMap_apply, LinearMap.add_apply, add_smul]
  have hop_C : ∀ (a : ℤ) (v : k ⊗[ℤ] Jp), op (MvPolynomial.C a) v = (a : k) • v := by
    intro a v
    have hlin : DistribSMul.toLinearMap ℤ Jp (MvPolynomial.C a : HeckeAlg) = a • LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [DistribSMul.toLinearMap_apply, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
        Submodule.coe_smul_of_tower]
      exact heckeModuleBar_C_smul a (x : JZero M')
    rw [hop_def, hlin, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply,
      LinearMap.id_apply]
    exact (Int.cast_smul_eq_zsmul k a v).symm

  have hop_congr : ∀ s t : HeckeAlg, heckeEvalBar hcomm s = heckeEvalBar hcomm t → op s = op t := by
    intro s t h
    rw [hop_def, hop_def]
    congr 1
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [DistribSMul.toLinearMap_apply, DistribSMul.toLinearMap_apply, Submodule.coe_smul, Submodule.coe_smul,
      heckeModuleBar_smul_def hcomm, heckeModuleBar_smul_def hcomm, h]

  let SC : HeckeAlg → Prop := fun t => ∃ c : k, ∀ w, PE w → op t w = c • w

  let pinned : Set HeckeAlg :=
    {t | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ((ℓ ∉ (↑S : Set ℕ) ∧ ¬ ℓ ∣ M') ∨ ℓ ∣ M') ∧ t = heckeGen ⟨ℓ, hℓ⟩}
  have hSC_adjoin : ∀ t ∈ Algebra.adjoin ℤ pinned, SC t := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨ℓ, hℓ, hcase, rfl⟩ := hx
      rcases hcase with ⟨hℓS, hℓM⟩ | hℓM
      · exact ⟨θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM), fun w hw => hw.1 ℓ hℓ hℓS hℓM⟩
      · exact ⟨θbar (CohCarrier.Gen.U ℓ hℓ hℓM), fun w hw => hw.2 ℓ hℓ hℓM⟩
    | algebraMap a =>
      refine ⟨(a : k), fun w _ => ?_⟩
      rw [MvPolynomial.algebraMap_eq]
      exact hop_C a w
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨c + d, fun w hw => ?_⟩
      rw [hop_add, LinearMap.add_apply, hc w hw, hd w hw, add_smul]
    | mul x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hy
      refine ⟨c * d, fun w hw => ?_⟩
      rw [hop_mul, LinearMap.comp_apply, hd w hw, LinearMap.map_smul, hc w hw, smul_smul, mul_comm]

  obtain ⟨Φ, hΦT, hΦU⟩ := ModularCurve.exists_ringHom_heckeAlgebra_heckeOperatorBar M'
  let Sd : Set ℕ := {r | r ∈ (↑S : Set ℕ) ∧ r.Prime ∧ ¬ r ∣ M'}
  have hSd_fin : Sd.Finite := (S.finite_toSet).subset (fun r hr => hr.1)
  have hSd_N : ∀ q ∈ Sd, q.Prime → ¬ q ∣ M' := fun q hq _ => hq.2.2
  have hSd_2 : p ∈ Sd → p ≠ 2 := fun _ => hp2
  have hmono : CuspForm.heckeAlgebra M' 2 Sd ≤ CuspForm.heckeAlgebra M' 2 (∅ : Set ℕ) :=
    CuspForm.heckeAlgebra_mono (Set.empty_subset _)
  have hbridge : ∀ (x : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M') 2))
      (hx : x ∈ CuspForm.heckeAlgebra M' 2 Sd),
      ∃ t' ∈ Algebra.adjoin ℤ pinned, Φ ⟨x, hmono hx⟩ = heckeEvalBar hcomm t' := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨ℓ, hℓ, hℓN, hℓSd, rfl⟩ | ⟨q, hqN, hq, hqSd, rfl⟩
      ·
        have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h => hℓSd ⟨h, hℓ, hℓN⟩
        refine ⟨heckeGen ⟨ℓ, hℓ⟩, Algebra.subset_adjoin ⟨ℓ, hℓ, Or.inl ⟨hℓS, hℓN⟩, rfl⟩, ?_⟩
        rw [heckeEvalBar_heckeGen]
        have := hΦT ⟨ℓ, hℓ⟩ hℓN (Set.notMem_empty _)
        rw [← this]
        rfl
      · refine ⟨heckeGen ⟨q, hq⟩, Algebra.subset_adjoin ⟨q, hq, Or.inr hqN, rfl⟩, ?_⟩
        rw [heckeEvalBar_heckeGen]
        have := hΦU ⟨q, hq⟩ hqN (Set.notMem_empty _)
        rw [← this]
        rfl
    | algebraMap a =>
      refine ⟨MvPolynomial.C a, Subalgebra.algebraMap_mem _ a, ?_⟩
      rw [heckeEvalBar_C]
      have h1 : (⟨algebraMap ℤ _ a, hmono (Subalgebra.algebraMap_mem _ a)⟩ : CuspForm.heckeAlgebra M' 2 (∅ : Set ℕ)) =
          algebraMap ℤ (CuspForm.heckeAlgebra M' 2 (∅ : Set ℕ)) a := Subtype.ext rfl
      rw [h1, Algebra.algebraMap_eq_smul_one, map_zsmul, map_one, zsmul_eq_mul, mul_one]
    | add y z hy hz ihy ihz =>
      obtain ⟨s, hs, hys⟩ := ihy
      obtain ⟨t, ht, hzt⟩ := ihz
      refine ⟨s + t, Subalgebra.add_mem _ hs ht, ?_⟩
      rw [map_add, ← hys, ← hzt, ← map_add]
      rfl
    | mul y z hy hz ihy ihz =>
      obtain ⟨s, hs, hys⟩ := ihy
      obtain ⟨t, ht, hzt⟩ := ihz
      refine ⟨s * t, Subalgebra.mul_mem _ hs ht, ?_⟩
      rw [map_mul, ← hys, ← hzt, ← map_mul]
      rfl

  have hunpinned : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∈ (↑S : Set ℕ) → ¬ ℓ ∣ M' → SC (heckeGen ⟨ℓ, hℓ⟩) := by
    intro ℓ hℓ hℓS hℓM

    obtain ⟨m, hpm, hmem⟩ := CuspForm.exists_not_dvd_and_smul_mem_heckeAlgebra_of_finite M'
      (CuspForm.hasIntegralStructure_two M') p Fact.out Sd hSd_fin hSd_N hSd_2
      (CuspForm.heckeAlgebra.T (N := M') (k := 2) (S := (∅ : Set ℕ)) hℓ hℓM (Set.notMem_empty _) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M') 2))
      (CuspForm.heckeAlgebra.T hℓ hℓM (Set.notMem_empty _)).2
    obtain ⟨t', ht', hΦt'⟩ := hbridge _ hmem

    have hΦm : Φ ⟨(m : ℤ) • (CuspForm.heckeAlgebra.T (N := M') (k := 2) (S := (∅ : Set ℕ)) hℓ hℓM (Set.notMem_empty _) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M') 2)), hmono hmem⟩ =
        heckeEvalBar hcomm (MvPolynomial.C (m : ℤ) * heckeGen ⟨ℓ, hℓ⟩) := by
      have h1 : (⟨(m : ℤ) • (CuspForm.heckeAlgebra.T (N := M') (k := 2) (S := (∅ : Set ℕ)) hℓ hℓM (Set.notMem_empty _) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M') 2)), hmono hmem⟩ : CuspForm.heckeAlgebra M' 2 (∅ : Set ℕ)) =
          (m : ℤ) • CuspForm.heckeAlgebra.T hℓ hℓM (Set.notMem_empty _) := rfl
      rw [h1, map_zsmul, hΦT ⟨ℓ, hℓ⟩ hℓM (Set.notMem_empty _), map_mul, heckeEvalBar_C, heckeEvalBar_heckeGen,
        zsmul_eq_mul]
    have hev : heckeEvalBar hcomm t' = heckeEvalBar hcomm (MvPolynomial.C (m : ℤ) * heckeGen ⟨ℓ, hℓ⟩) := by
      rw [← hΦt', ← hΦm]
    obtain ⟨c, hc⟩ := hSC_adjoin t' ht'
    have hmk : ((m : ℤ) : k) ≠ 0 := by
      rw [Int.cast_natCast, Ne, CharP.cast_eq_zero_iff k p]
      exact hpm
    refine ⟨((m : ℤ) : k)⁻¹ * c, fun w hw => ?_⟩
    have h := hc w hw
    rw [hop_congr _ _ hev, hop_mul, LinearMap.comp_apply, hop_C] at h

    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hmk, one_smul]

  have hgen : ∀ ℓ : Nat.Primes, SC (heckeGen ℓ) := by
    rintro ⟨ℓ, hℓ⟩
    by_cases hℓM : ℓ ∣ M'
    · exact ⟨θbar (CohCarrier.Gen.U ℓ hℓ hℓM), fun w hw => hw.2 ℓ hℓ hℓM⟩
    · by_cases hℓS : ℓ ∈ (↑S : Set ℕ)
      · exact hunpinned ℓ hℓ hℓS hℓM
      · exact ⟨θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM), fun w hw => hw.1 ℓ hℓ hℓS hℓM⟩
  choose cgen hcgen using hgen
  let χ : HeckeAlg →+* k := MvPolynomial.eval₂Hom (Int.castRingHom k) cgen
  have hχ : ∀ (t : HeckeAlg) (w : k ⊗[ℤ] Jp), PE w → op t w = χ t • w := by
    intro t w hw
    induction t using MvPolynomial.induction_on with
    | C a =>
      rw [hop_C]
      show (a : k) • w = (MvPolynomial.eval₂Hom (Int.castRingHom k) cgen (MvPolynomial.C a)) • w
      rw [MvPolynomial.eval₂Hom_C, eq_intCast]
    | add s t hs ht => rw [hop_add, LinearMap.add_apply, hs, ht, map_add, add_smul]
    | mul_X s ℓ hs =>
      rw [hop_mul, LinearMap.comp_apply]
      show (op s) ((op (heckeGen ℓ)) w) = _
      rw [hcgen ℓ w hw, LinearMap.map_smul, hs, smul_smul, map_mul, mul_comm (χ s)]
      congr 1
      show cgen ℓ * χ s = (MvPolynomial.eval₂Hom (Int.castRingHom k) cgen (MvPolynomial.X ℓ)) * χ s
      rw [MvPolynomial.eval₂Hom_X']

  have hχT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
      χ (heckeGen ⟨ℓ, hℓ⟩) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) := by
    intro ℓ hℓ hℓS hℓM
    have h1 := hχ (heckeGen ⟨ℓ, hℓ⟩) w₀ hPE₀
    rw [hw₀T ℓ hℓ hℓS hℓM] at h1
    exact (smul_left_injective k hw₀ h1).symm
  have hχU : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M'),
      χ (heckeGen ⟨q, hq⟩) = θbar (CohCarrier.Gen.U q hq hqM) := by
    intro q hq hqM
    have h1 := hχ (heckeGen ⟨q, hq⟩) w₀ hPE₀
    rw [hw₀U q hq hqM] at h1
    exact (smul_left_injective k hw₀ h1).symm

  haveI hJpfin : Finite Jp :=
    SolAN.finite_heckeTorsion M' p (Ideal.span {((p : ℕ) : HeckeAlg)}) (Ideal.subset_span rfl)

  let ψ : HeckeAlg →+* Module.End ℤ Jp := Module.toModuleEnd ℤ (S := HeckeAlg) Jp
  have hψ : ∀ (t : HeckeAlg) (x : Jp), ψ t x = t • x := fun t x => rfl
  haveI : Finite (Module.End ℤ Jp) :=
    Finite.of_injective (fun f : Module.End ℤ Jp => (f : Jp → Jp)) (fun f g h => LinearMap.ext (congrFun h))
  have hker : RingHom.ker ψ ≤ RingHom.ker χ := by
    intro t ht
    rw [RingHom.mem_ker] at ht ⊢
    have h0 : op t = 0 := by
      rw [hop_def]
      have : DistribSMul.toLinearMap ℤ Jp t = 0 := by
        apply LinearMap.ext
        intro x
        rw [DistribSMul.toLinearMap_apply, LinearMap.zero_apply, ← hψ, ht, LinearMap.zero_apply]
      rw [this, LinearMap.baseChange_zero]
    have h1 := hχ t w₀ hPE₀
    rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
    exact h1.resolve_right hw₀
  haveI hfinq : Finite (HeckeAlg ⧸ RingHom.ker χ) := by
    haveI : Finite (HeckeAlg ⧸ RingHom.ker ψ) :=
      Finite.of_equiv _ (RingHom.quotientKerEquivRange ψ).symm.toEquiv
    exact Finite.of_surjective (Ideal.Quotient.factor hker) (Ideal.Quotient.factor_surjective hker)
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  haveI hdom : IsDomain (HeckeAlg ⧸ RingHom.ker χ) := Ideal.Quotient.isDomain (RingHom.ker χ)
  have hmax : (RingHom.ker χ).IsMaximal := by
    apply Ideal.Quotient.maximal_of_isField
    exact Finite.isField_of_domain (HeckeAlg ⧸ RingHom.ker χ)

  refine ⟨RingHom.ker χ, hmax, RingHom.kerLift χ, ?_, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  · intro ℓ hℓ hℓS hℓM
    rw [RingHom.kerLift_mk]
    exact hχT ℓ hℓ hℓS hℓM
  · intro q hq hqM
    rw [RingHom.kerLift_mk]
    exact hχU q hq hqM
  · intro t w hwT hwU _
    rw [RingHom.kerLift_mk]
    exact hχ t w ⟨hwT, hwU⟩

end S_CohCarrier_exists_ideal_forall_heckeAlg_baseChange_eq_smul_of_exists_jZero_pTorsion_eigenvector
end P2MW
export P2MW.S_CohCarrier_exists_ideal_forall_heckeAlg_baseChange_eq_smul_of_exists_jZero_pTorsion_eigenvector (solution)

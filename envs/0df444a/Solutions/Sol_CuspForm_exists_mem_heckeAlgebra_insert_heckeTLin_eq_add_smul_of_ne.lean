-- Prove2me | solution 1 for CuspForm.exists_mem_heckeAlgebra_insert_heckeTLin_eq_add_smul_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e4f78c56-95c7-5db1-ac34-8544eb18023c

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jZero
import Theorems.Thm_ModularCurve_rep_tateModule_jZero_comm
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_natCard_torsion_jZero_eq_pow_finrank_periodLattice
import Theorems.Thm_ModularCurve_JZero_isOpen_stabilizer
import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_mem_heckeAlgebra_insert_heckeTLin_eq_add_smul_of_ne
p2m_attr_erase "instance" "ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D"
p2m_attr_erase "simp" "ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

open scoped TensorProduct Pointwise

namespace CuspForm
p2m_export "CuspForm" "sub_apply smul_apply coe_zero zero_apply coe_sub ext add_apply heckeAlgebra heckeTLin_mem_heckeAlgebra heckeAlgebra_mono heckeTLin HasIntegralStructure"
namespace RibetClaimOne
p2m_open "CuspForm"

section Lucas

variable {A : Type*} [Ring A]

def lucas (s c : A) : ℕ → A
  | 0 => 2
  | 1 => s
  | (k + 2) => s * lucas s c (k + 1) - c * lucas s c k

theorem lucas_zero (s c : A) : lucas s c 0 = 2 := rfl

theorem lucas_one (s c : A) : lucas s c 1 = s := rfl

theorem lucas_add_two (s c : A) (k : ℕ) :
    lucas s c (k + 2) = s * lucas s c (k + 1) - c * lucas s c k := rfl

theorem map_lucas {B : Type*} [Ring B] (f : A →+* B) (s c : A) :
    ∀ k, f (lucas s c k) = lucas (f s) (f c) k
  | 0 => by rw [lucas_zero, lucas_zero, map_ofNat]
  | 1 => rfl
  | (k + 2) => by
    rw [lucas_add_two, lucas_add_two, map_sub, map_mul, map_mul, map_lucas f s c k,
      map_lucas f s c (k + 1)]

theorem lucas_mem (B : Subalgebra ℤ A) {s c : A} (hs : s ∈ B) (hc : c ∈ B) :
    ∀ k, lucas s c k ∈ B
  | 0 => by rw [lucas_zero]; exact_mod_cast B.natCast_mem 2
  | 1 => hs
  | (k + 2) => B.sub_mem (B.mul_mem hs (lucas_mem B hs hc (k + 1)))
      (B.mul_mem hc (lucas_mem B hs hc k))

theorem lucas_pair {a b : A} (h : Commute a b) : ∀ k,
    lucas (a + b) (a * b) k = a ^ k + b ^ k ∧
      lucas (a + b) (a * b) (k + 1) = a ^ (k + 1) + b ^ (k + 1)
  | 0 => ⟨by rw [lucas_zero, pow_zero, pow_zero]; norm_num,
      by rw [lucas_one, pow_one, pow_one]⟩
  | (k + 1) => by
    obtain ⟨h0, h1⟩ := lucas_pair h k
    refine ⟨h1, ?_⟩
    rw [lucas_add_two, h1, h0]
    have e1 : a * b ^ (k + 1) = a * b * b ^ k := by rw [pow_succ', mul_assoc]
    have e2 : b * a ^ (k + 1) = a * b * a ^ k := by
      rw [pow_succ', ← mul_assoc, ← h.eq, mul_assoc]
    rw [add_mul, mul_add, mul_add, mul_add, e1, e2, pow_succ' a (k + 1), pow_succ' b (k + 1)]
    abel

theorem lucas_eq_pow_add_pow {a b : A} (h : Commute a b) (k : ℕ) :
    lucas (a + b) (a * b) k = a ^ k + b ^ k :=
  (lucas_pair h k).1

end Lucas

section ArtinRees

theorem exists_forall_mem_pow_smul_imp {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] (R : Submodule A M) (p : A) :
    ∃ d : ℕ, ∀ u ∈ R, (∃ v : M, u = (p ^ d) • v) → ∃ w ∈ R, u = p • w := by
  obtain ⟨k, hk⟩ := (Ideal.span ({p} : Set A)).exists_pow_inf_eq_pow_smul R
  refine ⟨k + 1, fun u hu hv => ?_⟩
  obtain ⟨v, hv⟩ := hv
  have h1 : u ∈ (Ideal.span ({p} : Set A)) ^ (k + 1) • (⊤ : Submodule A M) ⊓ R := by
    refine ⟨?_, hu⟩
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul (p ^ (k + 1)) ⊤, hv]
    exact Submodule.smul_mem_pointwise_smul v (p ^ (k + 1)) ⊤ Submodule.mem_top
  rw [hk (k + 1) (Nat.le_succ k), Nat.add_sub_cancel_left, pow_one,
    Submodule.ideal_span_singleton_smul p] at h1
  obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists u p _).1 h1
  exact ⟨w, hw.2, rfl⟩

end ArtinRees

section Descent

variable {p : ℕ} [Fact p.Prime]

theorem exists_eq_pow_smul_of_baseChange {Λ : Type*} [AddCommGroup Λ]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ Λ) (u : Module.End ℤ Λ) (d : ℕ)
    (h : ∀ x : Λ, ∃ z : ℤ_[p] ⊗[ℤ] Λ, u.baseChange ℤ_[p] (1 ⊗ₜ x) = ((p : ℤ_[p]) ^ d) • z) :
    ∃ v : Module.End ℤ Λ, u = ((p : ℤ) ^ d) • v := by
  classical
  have hdiv : ∀ i j, ((p : ℤ) ^ d) ∣ b.repr (u (b i)) j := by
    intro i j
    obtain ⟨z, hz⟩ := h (b i)
    rw [LinearMap.baseChange_tmul] at hz
    set B := Algebra.TensorProduct.basis ℤ_[p] b with hB
    have h1 : B.repr ((1 : ℤ_[p]) ⊗ₜ u (b i)) j = ((b.repr (u (b i)) j : ℤ) : ℤ_[p]) := by
      rw [hB, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply,
        algebraMap_int_eq, eq_intCast]
    have h2 : B.repr ((1 : ℤ_[p]) ⊗ₜ u (b i)) j = (p : ℤ_[p]) ^ d * B.repr z j := by
      rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul]
    have h3 : (p : ℤ_[p]) ^ d ∣ ((b.repr (u (b i)) j : ℤ) : ℤ_[p]) := by
      rw [← h1, h2]; exact Dvd.intro _ rfl
    have h4 := (PadicInt.pow_p_dvd_int_iff d (b.repr (u (b i)) j)).1 h3
    exact_mod_cast h4
  choose c hc using hdiv
  refine ⟨b.constr ℤ fun i => ∑ j, c i j • b j, b.ext fun i => ?_⟩
  rw [LinearMap.smul_apply, Module.Basis.constr_basis, Finset.smul_sum]
  conv_lhs => rw [← b.sum_repr (u (b i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc i j, smul_smul]

end Descent

section Deep

open IsLocalRing

variable (p : ℕ) [Fact p.Prime] (T : Type*) [AddCommGroup T] [Module ℤ_[p] T]

def deep (d : ℕ) : Submodule ℤ_[p] T := (maximalIdeal ℤ_[p] ^ d) • ⊤

variable {p T}

theorem deep_eq (d : ℕ) : deep p T d = ((p : ℤ_[p]) ^ d) • (⊤ : Submodule ℤ_[p] T) := by
  unfold deep
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul]

theorem mem_deep_iff (d : ℕ) (x : T) : x ∈ deep p T d ↔ ∃ z : T, x = ((p : ℤ_[p]) ^ d) • z := by
  rw [deep_eq, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, rfl⟩; exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩; exact ⟨z, Submodule.mem_top, rfl⟩

theorem mem_deep_of_mem {T' : Type*} [AddCommGroup T'] [Module ℤ_[p] T'] (f : T →ₗ[ℤ_[p]] T')
    {d : ℕ} {x : T} (hx : x ∈ deep p T d) : f x ∈ deep p T' d := by
  have h : (deep p T d).map f ≤ deep p T' d := by
    unfold deep
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h ⟨x, hx, rfl⟩

theorem smul_mem_deep {d : ℕ} {c : ℤ_[p]} (hc : c ∈ maximalIdeal ℤ_[p] ^ d) (x : T) :
    c • x ∈ deep p T d :=
  Submodule.smul_mem_smul hc Submodule.mem_top

def IsSmall (d : ℕ) (u : Module.End ℤ_[p] T) : Prop := ∀ x, u x ∈ deep p T d

theorem IsSmall.add {d : ℕ} {u v : Module.End ℤ_[p] T} (hu : IsSmall d u) (hv : IsSmall d v) :
    IsSmall d (u + v) := fun x => Submodule.add_mem _ (hu x) (hv x)

theorem IsSmall.sub {d : ℕ} {u v : Module.End ℤ_[p] T} (hu : IsSmall d u) (hv : IsSmall d v) :
    IsSmall d (u - v) := fun x => Submodule.sub_mem _ (hu x) (hv x)

theorem IsSmall.neg {d : ℕ} {u : Module.End ℤ_[p] T} (hu : IsSmall d u) : IsSmall d (-u) :=
  fun x => Submodule.neg_mem _ (hu x)

theorem IsSmall.nsmul {d : ℕ} {u : Module.End ℤ_[p] T} (hu : IsSmall d u) (k : ℕ) :
    IsSmall d (k • u) := fun x => by
  rw [LinearMap.smul_apply]; exact Submodule.smul_of_tower_mem _ k (hu x)

theorem IsSmall.mul_left {d : ℕ} {u : Module.End ℤ_[p] T} (v : Module.End ℤ_[p] T)
    (hu : IsSmall d u) : IsSmall d (v * u) := fun x => mem_deep_of_mem v (hu x)

theorem IsSmall.mul_right {d : ℕ} {u : Module.End ℤ_[p] T} (v : Module.End ℤ_[p] T)
    (hu : IsSmall d u) : IsSmall d (u * v) := fun x => hu (v x)

theorem isSmall_smul_of_mem {d : ℕ} {c : ℤ_[p]} (hc : c ∈ maximalIdeal ℤ_[p] ^ d)
    (u : Module.End ℤ_[p] T) : IsSmall d (c • u) := fun x => by
  rw [LinearMap.smul_apply]; exact smul_mem_deep hc (u x)

end Deep

section EndAlgebra

open IsLocalRing

variable {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
  {G : Type*} [Group G]

theorem isSmall_sub_lucas (ρ : G →* Module.End ℤ_[p] T) (Tr Tq : Module.End ℤ_[p] T)
    (σ τ g h : G) (r q n d : ℕ) (hFn : (g * τ * g⁻¹) ^ n = h * σ)
    (hESσ : ∀ x, ρ σ (ρ σ x) - Tr (ρ σ x) + r • x = 0)
    (hESτ : ∀ x, ρ τ (ρ τ x) - Tq (ρ τ x) + q • x = 0)
    (hcomm : ∀ x, ρ g (Tq x) = Tq (ρ g x))
    (hsm : IsSmall d (ρ (h * σ) - ρ σ))
    (hmemI : ((r : ℤ_[p]) - (q : ℤ_[p]) ^ n) ∈ maximalIdeal ℤ_[p] ^ d) :
    IsSmall d (Tr - lucas Tq (q : Module.End ℤ_[p] T) n) := by
  set F : G := g * τ * g⁻¹ with hF
  set Φ : Module.End ℤ_[p] T := ρ σ with hΦ
  set Φ' : Module.End ℤ_[p] T := ρ σ⁻¹ with hΦ'
  set Ψ : Module.End ℤ_[p] T := ρ F with hΨ
  set Ψ' : Module.End ℤ_[p] T := ρ F⁻¹ with hΨ'
  have hΦΦ' : Φ * Φ' = 1 := by rw [hΦ, hΦ', ← map_mul, mul_inv_cancel, map_one]
  have hΦ'Φ : Φ' * Φ = 1 := by rw [hΦ, hΦ', ← map_mul, inv_mul_cancel, map_one]
  have hΨΨ' : Ψ * Ψ' = 1 := by rw [hΨ, hΨ', ← map_mul, mul_inv_cancel, map_one]
  have hΨ'Ψ : Ψ' * Ψ = 1 := by rw [hΨ, hΨ', ← map_mul, inv_mul_cancel, map_one]
  have hΨn : Ψ ^ n = ρ (h * σ) := by rw [hΨ, ← map_pow, hFn]
  have hΨnΨ'n : Ψ ^ n * Ψ' ^ n = 1 := by
    rw [hΨ, hΨ', ← map_pow, ← map_pow, ← map_mul, inv_pow, mul_inv_cancel, map_one]

  have hTrE : Tr = Φ + r • Φ' := by
    refine LinearMap.ext fun y => ?_
    have e := hESσ (Φ' y)
    have hy : Φ (Φ' y) = y := by
      rw [← Module.End.mul_apply, hΦΦ', Module.End.one_apply]
    rw [hy] at e
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    rw [sub_add_eq_add_sub, sub_eq_zero] at e
    exact e.symm
  have hESF : ∀ y : T, Ψ (Ψ y) - Tq (Ψ y) + q • y = 0 := by
    intro y
    have hgg : ∀ z, ρ g⁻¹ (ρ g z) = z := fun z => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hgg' : ρ g (ρ g⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have hΨy : ∀ z, Ψ z = ρ g (ρ τ (ρ g⁻¹ z)) := fun z => by
      rw [hΨ, hF, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    have e := congrArg (ρ g) (hESτ (ρ g⁻¹ y))
    rw [map_zero, map_add, map_sub, map_nsmul, hgg', hcomm] at e
    rw [hΨy, hΨy, hgg]
    exact e
  have hTqE : Tq = Ψ + q • Ψ' := by
    refine LinearMap.ext fun y => ?_
    have e := hESF (Ψ' y)
    have hy : Ψ (Ψ' y) = y := by
      rw [← Module.End.mul_apply, hΨΨ', Module.End.one_apply]
    rw [hy] at e
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    rw [sub_add_eq_add_sub, sub_eq_zero] at e
    exact e.symm

  have hluc : lucas Tq (q : Module.End ℤ_[p] T) n = Ψ ^ n + q ^ n • Ψ' ^ n := by
    have hab : Ψ * (q • Ψ') = (q : Module.End ℤ_[p] T) := by
      rw [mul_smul_comm, hΨΨ', nsmul_one]
    have hc : Commute Ψ (q • Ψ') := by
      change Ψ * (q • Ψ') = (q • Ψ') * Ψ
      rw [mul_smul_comm, smul_mul_assoc, hΨΨ', hΨ'Ψ]
    rw [hTqE, ← hab, lucas_eq_pow_add_pow hc, smul_pow]

  have hsm1 : IsSmall d (Ψ ^ n - Φ) := by rw [hΨn]; exact hsm
  have hsm2 : IsSmall d (Φ' - Ψ' ^ n) := by
    have e : Φ' - Ψ' ^ n = Φ' * (Ψ ^ n - Φ) * Ψ' ^ n := by
      rw [mul_sub, sub_mul, mul_assoc Φ' (Ψ ^ n), hΨnΨ'n, mul_one, hΦ'Φ, one_mul]
    rw [e]
    exact (hsm1.mul_left Φ').mul_right (Ψ' ^ n)
  have hsm3 : IsSmall d (r • Ψ' ^ n - q ^ n • Ψ' ^ n) := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p] r, ← Nat.cast_smul_eq_nsmul ℤ_[p] (q ^ n), ← sub_smul,
      Nat.cast_pow]
    exact isSmall_smul_of_mem hmemI _

  have hdecomp : Tr - lucas Tq (q : Module.End ℤ_[p] T) n =
      -(Ψ ^ n - Φ) + (r • (Φ' - Ψ' ^ n) + (r • Ψ' ^ n - q ^ n • Ψ' ^ n)) := by
    rw [hTrE, hluc, smul_sub]
    abel
  rw [hdecomp]
  exact hsm1.neg.add ((hsm2.nsmul r).add hsm3)

theorem isSmall_map_sub_lucas {A : Type*} [Ring A] (f : A →+* Module.End ℤ_[p] T) (a s : A)
    (q n d : ℕ) (h : IsSmall d (f a - lucas (f s) (q : Module.End ℤ_[p] T) n)) :
    IsSmall d (f (a - lucas s (q : A) n)) := by
  rw [map_sub, map_lucas, map_natCast]
  exact h

end EndAlgebra

section Faithful

open ModularCurve

theorem cuspHeckeRep_eq_zero_of_periodLatticeHeckeEnd_eq_zero (N : ℕ) [NeZero N] (t : HeckeAlg)
    (ht : periodLatticeHeckeEnd N t = 0) : cuspHeckeRep N t = 0 := by
  obtain ⟨n, b, -, hspan⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  have hst := ModularCurve.periodLatticeHeckeStable N

  have hΛ : ∀ x : periodLattice N, dualHeckeRep N t (x : Module.Dual ℂ _) = 0 := by
    intro x
    have hx := LinearMap.congr_fun ht x
    rw [LinearMap.zero_apply] at hx
    rw [← coe_periodLatticeHeckeEnd_apply hst t x, hx, Submodule.coe_zero]

  have hD : ∀ φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      dualHeckeRep N t φ = 0 := by
    intro φ
    have hφ : φ ∈ Submodule.span ℝ (Set.range fun i =>
        ((b i : periodLattice N) : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) := by
      rw [hspan]; trivial
    refine Submodule.span_induction (p := fun φ _ => dualHeckeRep N t φ = 0) ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨i, rfl⟩; exact hΛ (b i)
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [LinearMap.map_smul_of_tower, hx, smul_zero]

  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  have := LinearMap.congr_fun (hD φ) f
  rwa [dualHeckeRep_apply_apply, LinearMap.zero_apply] at this

end Faithful

section Galois

open ModularCurve IsLocalRing

theorem isIntegral_algebraicClosure_rat : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := by
  have h := Subsingleton.elim (AlgebraicClosure.instAlgebra ℚ) (DivisionRing.toRatAlgebra)
  have := AlgebraicClosure.isAlgebraic ℚ
  rw [h] at this
  exact Algebra.IsAlgebraic.isIntegral

theorem exists_isPrimitiveRoot {m : ℕ} (hm : 0 < m) :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ m := by
  haveI : NeZero ((m : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic m (AlgebraicClosure ℚ))
    (Polynomial.degree_cyclotomic_pos m _ hm).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

theorem frobenius_pow_apply_eq_pow {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {q m : ℕ}
    (hA : A.LiesOverPrime q) (hτ : A.IsFrobeniusAt τ q) (hm : m.Coprime q) :
    ∀ (n : ℕ) (ζ : AlgebraicClosure ℚ), ζ ^ m = 1 → (τ ^ n) ζ = ζ ^ (q ^ n)
  | 0, ζ, _ => by rw [pow_zero, pow_zero, pow_one, AlgEquiv.one_apply]
  | (n + 1), ζ, hζ => by
    rw [pow_succ, AlgEquiv.mul_apply,
      ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ q m hA hτ hm ζ hζ, map_pow,
      frobenius_pow_apply_eq_pow hA hτ hm n ζ hζ, ← pow_mul, ← pow_succ]

theorem zsmul_smul_eq_zero {M : Type*} [AddCommGroup M] {G : Type*} [Monoid G]
    [DistribMulAction G M] (g : G) {n : ℤ} {y : M} (hy : n • y = 0) : n • g • y = 0 := by
  have e := map_zsmul (DistribSMul.toAddMonoidHom M g) n y
  rw [DistribSMul.toAddMonoidHom_apply, DistribSMul.toAddMonoidHom_apply] at e
  rw [← e, hy, smul_zero]

local notation "𝒢" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

local notation "ρ" =>
  TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem exists_isSmall_tateHeckeRep {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (hrN : ¬ r ∣ N)
    {M₀ : ℕ} (hM₀ : 0 < M₀) (hNM : N ∣ M₀) (hpM : p ∣ M₀) (d : ℕ) :
    letI := ModularCurve.heckeModuleBar N
    ∃ (q : ℕ) (hq : q.Prime) (n : ℕ), ¬ q ∣ M₀ ∧
      IsSmall d (tateHeckeRep p (JZero N)
        (heckeGen ⟨r, hr⟩ - lucas (heckeGen ⟨q, hq⟩) (q : HeckeAlg) n)) := by
  classical
  letI := ModularCurve.heckeModuleBar N
  have hp : p.Prime := Fact.out
  have hcommN := ModularCurve.heckeOperatorsCommuteBar N

  obtain ⟨A, σ, hA, hσ⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨r, hr⟩
  have hpd : 0 < p ^ d := pow_pos hp.pos d
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hpd
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hpd.ne'

  obtain ⟨Tor, hTor⟩ : ∃ Tor : Set (JZero N), Tor =
      ((AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ d) :
        AddSubgroup (JZero N)) : Set (JZero N)) := ⟨_, rfl⟩
  have hmemTor : ∀ y : JZero N, y ∈ Tor ↔ ((p ^ d : ℕ) : ℤ) • y = 0 := fun y => by
    rw [hTor, SetLike.mem_coe]; exact AlgebraicCurve.Pic0.mem_torsion
  have hTorfin : Tor.Finite := by
    haveI : Finite (AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
        (modularFunctionFieldBar N) (p ^ d)) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [ModularCurve.natCard_torsion_jZero_eq_pow_finrank_periodLattice N (p ^ d) hpd.ne']
      exact pow_ne_zero _ hpd.ne'
    rw [hTor]
    exact Set.toFinite _

  let H : Subgroup 𝒢 :=
    { carrier := {g | (∀ y ∈ Tor, g • y = y) ∧ g ζ = ζ}
      mul_mem' := by
        rintro g g' ⟨hg, hgζ⟩ ⟨hg', hg'ζ⟩
        exact ⟨fun y hy => by rw [mul_smul, hg' y hy, hg y hy],
          by rw [AlgEquiv.mul_apply, hg'ζ, hgζ]⟩
      one_mem' := ⟨fun y _ => one_smul _ _, rfl⟩
      inv_mem' := by
        rintro g ⟨hg, hgζ⟩
        refine ⟨fun y hy => ?_, ?_⟩
        · conv_lhs => rw [← hg y hy]
          rw [inv_smul_smul]
        · conv_lhs => rw [← hgζ]
          rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] }
  have hHmem : ∀ g : 𝒢, g ∈ H ↔ (∀ y ∈ Tor, g • y = y) ∧ g ζ = ζ := fun g => Iff.rfl
  have hHopen : IsOpen (H : Set 𝒢) := by
    haveI := isIntegral_algebraicClosure_rat
    have hset : (H : Set 𝒢) =
        (⋂ y ∈ Tor, ((MulAction.stabilizer 𝒢 y : Subgroup 𝒢) : Set 𝒢)) ∩
          ((MulAction.stabilizer 𝒢 ζ : Subgroup 𝒢) : Set 𝒢) := by
      ext g
      simp only [SetLike.mem_coe, hHmem, Set.mem_inter_iff, Set.mem_iInter₂,
        MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    rw [hset]
    exact (hTorfin.isOpen_biInter fun y _ => ModularCurve.JZero.isOpen_stabilizer N y).inter
      (stabilizer_isOpen_of_isIntegral ζ)

  obtain ⟨q, A', τ, g, n, hq, hqM, hA', hτ, hmem⟩ :=
    H.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen hHopen σ hM₀
  refine ⟨q, hq, n, hqM, ?_⟩
  have hqp : q ≠ p := fun h => hqM (h ▸ hpM)
  have hqNp : ¬ q ∣ N * p := by
    intro h
    rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact hqM (h.trans hNM)
    · exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 h)
  have hrNp : ¬ r ∣ N * p := by
    intro h
    rcases (Nat.Prime.dvd_mul hr).1 h with h | h
    · exact hrN h
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 h)

  obtain ⟨h, hh⟩ : ∃ h : 𝒢, h = g * τ ^ n * g⁻¹ * σ⁻¹ := ⟨_, rfl⟩
  rw [← hh] at hmem
  have hhH : (∀ y ∈ Tor, h • y = y) ∧ h ζ = ζ := (hHmem h).1 hmem
  have hFn : (g * τ * g⁻¹) ^ n = h * σ := by rw [conj_pow, hh, inv_mul_cancel_right]

  have hcopq : (p ^ d).Coprime q :=
    Nat.Coprime.pow_left d ((Nat.coprime_primes hp hq).2 (Ne.symm hqp))
  have hcopr : (p ^ d).Coprime r :=
    Nat.Coprime.pow_left d ((Nat.coprime_primes hp hr).2 (Ne.symm hrp))
  have hζpow : ζ ^ (q ^ n) = ζ ^ r := by
    have e1 : ((g * τ * g⁻¹) ^ n) ζ = ζ ^ (q ^ n) := by
      have hζ₁ : (g⁻¹ ζ) ^ (p ^ d) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
      rw [conj_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
        frobenius_pow_apply_eq_pow hA' hτ hcopq n _ hζ₁, map_pow, ← AlgEquiv.mul_apply,
        mul_inv_cancel, AlgEquiv.one_apply]
    have e2 : ((g * τ * g⁻¹) ^ n) ζ = ζ ^ r := by
      rw [hFn, AlgEquiv.mul_apply,
        ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ r (p ^ d) hA hσ hcopr ζ
          hζ.pow_eq_one, map_pow, hhH.2]
    rw [← e1, e2]
  have hdvd : ((p ^ d : ℕ) : ℤ) ∣ (r : ℤ) - (q : ℤ) ^ n := by
    have h1 : ζ ^ ((r : ℤ) - (q : ℤ) ^ n) = 1 := by
      rw [zpow_sub₀ hζ0, zpow_natCast, ← Int.natCast_pow, zpow_natCast, hζpow,
        div_self (pow_ne_zero _ hζ0)]
    exact (hζ.zpow_eq_one_iff_dvd _).1 h1
  have hmemI : ((r : ℤ_[p]) - (q : ℤ_[p]) ^ n) ∈ maximalIdeal ℤ_[p] ^ d := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    have := (Int.castRingHom ℤ_[p]).map_dvd hdvd
    simpa using this

  have hsm : IsSmall d (ρ (h * σ) - ρ σ) := by
    intro x
    change (ρ (h * σ) - ρ σ) x ∈
      (maximalIdeal ℤ_[p] ^ d) • (⊤ : Submodule ℤ_[p] (TateModule p (JZero N)))
    rw [← TateModule.proj_eq_zero_iff, TateModule.proj_apply, LinearMap.sub_apply,
      TateModule.coe_sub, Pi.sub_apply, sub_eq_zero]

    have e1 : ((ρ (h * σ) x : TateModule p (JZero N)) : ℕ → JZero N) d =
        h • σ • (x : ℕ → JZero N) d := mul_smul h σ _
    have e2 : ((ρ σ x : TateModule p (JZero N)) : ℕ → JZero N) d = σ • (x : ℕ → JZero N) d := rfl
    exact e1.trans
      ((hhH.1 _ ((hmemTor _).2 (zsmul_smul_eq_zero σ (TateModule.torsion x d)))).trans e2.symm)

  have hESσ := ModularCurve.frobeniusQuadratic_tateModule_jZero N p hcommN hr hrNp A hA σ hσ
  have hESτ := ModularCurve.frobeniusQuadratic_tateModule_jZero N p hcommN hq hqNp A' hA' τ hτ
  have hcomm := fun (x : TateModule p (JZero N)) =>
    ModularCurve.rep_tateModule_jZero_comm N p hcommN g (heckeGen ⟨q, hq⟩) x

  have h' := isSmall_sub_lucas (TateModule.rep p (JZero N) 𝒢)
    (TateModule.rep p (JZero N) HeckeAlg (heckeGen ⟨r, hr⟩))
    (TateModule.rep p (JZero N) HeckeAlg (heckeGen ⟨q, hq⟩)) σ τ g h r q n d hFn hESσ hESτ
    hcomm hsm hmemI
  exact isSmall_map_sub_lucas (tateHeckeRep p (JZero N)) (heckeGen ⟨r, hr⟩) (heckeGen ⟨q, hq⟩)
    q n d h'

end Galois

section Assembly

open ModularCurve

theorem exists_exponent {Λ : Type*} [AddCommGroup Λ] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ Λ) (θ : HeckeAlg →+* Module.End ℤ Λ) {E' : Type*} [Ring E']
    (𝔠 : HeckeAlg →+* E') (B : Subalgebra ℤ E') (hfaith : ∀ t, θ t = 0 → 𝔠 t = 0)
    (p : ℕ) [Fact p.Prime] :
    ∃ d : ℕ, ∀ t₀ : HeckeAlg, 𝔠 t₀ ∈ B →
      (∀ x : Λ, ∃ z : ℤ_[p] ⊗[ℤ] Λ,
        (θ t₀).baseChange ℤ_[p] (1 ⊗ₜ x) = ((p : ℤ_[p]) ^ d) • z) →
      ∃ t₁ : HeckeAlg, 𝔠 t₁ ∈ B ∧ 𝔠 t₀ = (p : ℤ) • 𝔠 t₁ := by
  classical
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  haveI : Module.Finite ℤ (Module.End ℤ Λ) := Module.Finite.linearMap ℤ ℤ Λ Λ

  let R : Submodule ℤ (Module.End ℤ Λ) :=
    { carrier := {u | ∃ t : HeckeAlg, 𝔠 t ∈ B ∧ θ t = u}
      add_mem' := by
        rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
        exact ⟨t + t', by rw [map_add]; exact Subalgebra.add_mem _ ht ht', map_add _ _ _⟩
      zero_mem' := ⟨0, by rw [map_zero]; exact Subalgebra.zero_mem _, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨t, ht, rfl⟩
        refine ⟨(c : HeckeAlg) * t, ?_, ?_⟩
        · rw [map_mul, map_intCast]
          exact Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ c) ht
        · rw [map_mul, map_intCast, ← zsmul_eq_mul] }
  have hRmem : ∀ u, u ∈ R ↔ ∃ t : HeckeAlg, 𝔠 t ∈ B ∧ θ t = u := fun u => Iff.rfl
  obtain ⟨d, hd⟩ := exists_forall_mem_pow_smul_imp R (p : ℤ)
  refine ⟨d, fun t₀ ht₀ hbc => ?_⟩
  obtain ⟨v, hv⟩ := exists_eq_pow_smul_of_baseChange b (θ t₀) d hbc
  obtain ⟨w, hwR, hw⟩ := hd (θ t₀) ((hRmem _).2 ⟨t₀, ht₀, rfl⟩) ⟨v, hv⟩
  obtain ⟨t₁, ht₁, rfl⟩ := (hRmem _).1 hwR

  have hker : θ (t₀ - (p : HeckeAlg) * t₁) = 0 := by
    rw [map_sub, map_mul, map_natCast, sub_eq_zero, ← nsmul_eq_mul, ← natCast_zsmul]
    exact hw
  have hzero := hfaith _ hker
  refine ⟨t₁, ht₁, ?_⟩
  rw [map_sub, map_mul, map_natCast, sub_eq_zero, ← nsmul_eq_mul, ← natCast_zsmul] at hzero
  exact hzero

theorem main (N : ℕ) [NeZero N] (p r : ℕ) (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p)
    (hrN : ¬ r ∣ N) (S : Set ℕ) (hS : S.Finite) (hrS : r ∉ S) :
    ∃ t' ∈ CuspForm.heckeAlgebra N 2 (insert r S),
      ∃ t'' ∈ CuspForm.heckeAlgebra N 2 S,
        (CuspForm.heckeTLin 2 hr hrN :
            Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = t' + (p : ℤ) • t'' := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  letI := ModularCurve.heckeModuleBar N
  have hst := ModularCurve.periodLatticeHeckeStable N

  obtain ⟨m, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  obtain ⟨d, hd⟩ := exists_exponent b (periodLatticeHeckeEnd N) (cuspHeckeRep N)
    (CuspForm.heckeAlgebra N 2 S) (cuspHeckeRep_eq_zero_of_periodLatticeHeckeEnd_eq_zero N) p

  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = ∏ s ∈ hS.toFinset, max s 1 := ⟨_, rfl⟩
  have hPpos : 0 < P := by
    rw [hP]; exact Finset.prod_pos fun s _ => lt_max_of_lt_right Nat.one_pos
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, M₀ = N * p * r * P := ⟨_, rfl⟩
  have hM₀pos : 0 < M₀ := by
    rw [hM₀]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) hp.pos)
      hr.pos) hPpos
  have hNM : N ∣ M₀ := ⟨p * r * P, by rw [hM₀]; ring⟩
  have hpM : p ∣ M₀ := ⟨N * r * P, by rw [hM₀]; ring⟩
  have hrM : r ∣ M₀ := ⟨N * p * P, by rw [hM₀]; ring⟩
  have hPM : P ∣ M₀ := ⟨N * p * r, by rw [hM₀]; ring⟩

  obtain ⟨q, hq, n, hqM, hsmall⟩ := exists_isSmall_tateHeckeRep N p hr hrp hrN hM₀pos hNM hpM d
  have hqN : ¬ q ∣ N := fun h => hqM (h.trans hNM)
  have hqr : q ≠ r := fun h => hqM (h ▸ hrM)
  have hqS : q ∉ S := by
    intro hqS'
    apply hqM
    refine Dvd.dvd.trans ?_ hPM
    have h1 : max q 1 ∣ P := by
      rw [hP]; exact Finset.dvd_prod_of_mem (fun s => max s 1) (hS.mem_toFinset.2 hqS')
    rwa [max_eq_left hq.one_lt.le] at h1
  have hqrS : q ∉ insert r S := by
    rintro (h | h)
    · exact hqr h
    · exact hqS h

  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : HeckeAlg,
      t₀ = heckeGen ⟨r, hr⟩ - lucas (heckeGen ⟨q, hq⟩) (q : HeckeAlg) n := ⟨_, rfl⟩
  rw [← ht₀] at hsmall
  obtain ⟨e, he⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
      N p (ModularCurve.heckeInputsAll N) (ModularCurve.heckeOperatorsCommuteBar N) hst
  have hbc : ∀ x : periodLattice N, ∃ z : ℤ_[p] ⊗[ℤ] periodLattice N,
      (periodLatticeHeckeEnd N t₀).baseChange ℤ_[p] (1 ⊗ₜ x) = ((p : ℤ_[p]) ^ d) • z := by
    intro x
    refine (mem_deep_iff d _).1 ?_
    have h1 := he t₀ (e.symm ((1 : ℤ_[p]) ⊗ₜ x))
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [← h1]
    exact mem_deep_of_mem e.toLinearMap (hsmall _)

  have hgen_q : cuspHeckeRep N (heckeGen ⟨q, hq⟩) = CuspForm.heckeTLin 2 hq hqN := by
    rw [cuspHeckeRep_heckeGen, cuspHeckeGen_of_not_dvd N ⟨q, hq⟩ hqN]
  have hgen_r : cuspHeckeRep N (heckeGen ⟨r, hr⟩) = CuspForm.heckeTLin 2 hr hrN := by
    rw [cuspHeckeRep_heckeGen, cuspHeckeGen_of_not_dvd N ⟨r, hr⟩ hrN]
  have hlucS' : cuspHeckeRep N (lucas (heckeGen ⟨q, hq⟩) (q : HeckeAlg) n) ∈
      CuspForm.heckeAlgebra N 2 (insert r S) := by
    have h1 : cuspHeckeRep N (heckeGen ⟨q, hq⟩) ∈ CuspForm.heckeAlgebra N 2 (insert r S) := by
      rw [hgen_q]; exact CuspForm.heckeTLin_mem_heckeAlgebra hq hqN hqrS
    have h2 : cuspHeckeRep N (q : HeckeAlg) ∈ CuspForm.heckeAlgebra N 2 (insert r S) := by
      rw [map_natCast]; exact Subalgebra.natCast_mem _ q
    have h3 := lucas_mem _ h1 h2 n
    rwa [← map_lucas] at h3
  have ht₀S : cuspHeckeRep N t₀ ∈ CuspForm.heckeAlgebra N 2 S := by
    have h1 : cuspHeckeRep N (heckeGen ⟨r, hr⟩) ∈ CuspForm.heckeAlgebra N 2 S := by
      rw [hgen_r]; exact CuspForm.heckeTLin_mem_heckeAlgebra hr hrN hrS
    have h2 : cuspHeckeRep N t₀ = cuspHeckeRep N (heckeGen ⟨r, hr⟩) -
        cuspHeckeRep N (lucas (heckeGen ⟨q, hq⟩) (q : HeckeAlg) n) := by
      rw [ht₀, map_sub]
    rw [h2]
    exact Subalgebra.sub_mem _ h1 (CuspForm.heckeAlgebra_mono (Set.subset_insert r S) hlucS')

  obtain ⟨t₁, ht₁S, hmain⟩ := hd t₀ ht₀S hbc
  refine ⟨cuspHeckeRep N (lucas (heckeGen ⟨q, hq⟩) (q : HeckeAlg) n), hlucS', cuspHeckeRep N t₁,
    ht₁S, ?_⟩
  have hsplit : heckeGen ⟨r, hr⟩ = t₀ + lucas (heckeGen ⟨q, hq⟩) (q : HeckeAlg) n := by
    rw [ht₀, sub_add_cancel]
  rw [← hgen_r, hsplit, map_add, hmain, add_comm]

end Assembly

end CuspForm.RibetClaimOne

end

set_option linter.unusedVariables false in

theorem solution (N : ℕ) [NeZero N] (hint : CuspForm.HasIntegralStructure N 2)
    (p r : ℕ) (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) (hrN : ¬ r ∣ N)
    (S : Set ℕ) (hS : S.Finite) (hrS : r ∉ S) :
    ∃ t' ∈ CuspForm.heckeAlgebra N 2 (insert r S),
      ∃ t'' ∈ CuspForm.heckeAlgebra N 2 S,
        (CuspForm.heckeTLin 2 hr hrN :
            Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = t' + (p : ℤ) • t'' :=
  CuspForm.RibetClaimOne.main N p r hp hr hrp hrN S hS hrS

end S_CuspForm_exists_mem_heckeAlgebra_insert_heckeTLin_eq_add_smul_of_ne
end P2MW
export P2MW.S_CuspForm_exists_mem_heckeAlgebra_insert_heckeTLin_eq_add_smul_of_ne (solution)

-- Prove2me | solution 1 for CuspForm.qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8a5049da-966d-550e-9898-8b52c4f02a7e

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
import Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jZero
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Theorems.Thm_ModularCurve_JZero_exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul
import Theorems.Thm_AlgebraicCurve_Pic0_exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
import Theorems.Thm_ModularCurve_frobeniusInputsModL
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_ModularCurve_reductionModL_smul_of_isFrobeniusAt
import Theorems.Thm_ModularCurve_eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Polynomial

noncomputable section

namespace CuspForm
p2m_export "CuspForm" "sub_apply mk smul_apply coe_zero zero_apply ext coe_smul add_apply coe_add IsNormalizedEigenform heckeTLin IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul"
namespace NoEigenvalueOneAddPrime
p2m_open "CuspForm"

section Nonvanishing

variable {N : ℕ}

theorem qCoeff_coe_zero (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) n = 0 := by
  simp [ModularFormClass.qCoeff, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero]

theorem ne_zero_of_isNormalizedEigenform {h : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hh : h.IsNormalizedEigenform) : h ≠ 0 := by
  rintro rfl
  have h1 := hh.qCoeff_one
  rw [qCoeff_coe_zero] at h1
  exact zero_ne_one h1

end Nonvanishing

section Lattice

open ModularCurve

variable (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime)

def latticeHecke : Module.End ℤ (periodLattice N) :=
  periodLatticeHeckeEnd N (heckeGen ⟨p, hp⟩)

theorem coe_latticeHecke_apply_eval (hpN : ¬ p ∣ N) (x : periodLattice N)
    (h : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hh : h.IsNormalizedEigenform) :
    ((latticeHecke N hp x : periodLattice N) : Module.Dual ℂ _) h =
      ModularFormClass.qCoeff h p * (x : Module.Dual ℂ _) h := by
  rw [latticeHecke, coe_periodLatticeHeckeEnd_apply (ModularCurve.periodLatticeHeckeStable N),
    dualHeckeRep_apply_apply, cuspHeckeRep_heckeGen, cuspHeckeGen_of_not_dvd N ⟨p, hp⟩ hpN]
  change (x : Module.Dual ℂ _) (CuspForm.heckeTLin 2 hp hpN h) = _
  rw [CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul N h hh p hp hpN, map_smul,
    smul_eq_mul]

theorem coe_aeval_latticeHecke_apply_eval (hpN : ¬ p ∣ N) (χ : ℤ[X]) (x : periodLattice N)
    (h : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hh : h.IsNormalizedEigenform) :
    ((aeval (latticeHecke N hp) χ x : periodLattice N) : Module.Dual ℂ _) h =
      (χ.map (Int.castRingHom ℂ)).eval (ModularFormClass.qCoeff h p) * (x : Module.Dual ℂ _) h := by
  induction χ using Polynomial.induction_on generalizing x with
  | C a =>
    rw [aeval_C, Module.algebraMap_end_apply, Submodule.coe_smul, LinearMap.smul_apply,
      zsmul_eq_mul, Polynomial.map_C, eval_C, eq_intCast]
  | add f g hf hg =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, LinearMap.add_apply, hf, hg,
      Polynomial.map_add, eval_add, add_mul]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, aeval_X, ih,
      coe_latticeHecke_apply_eval N hp hpN x h hh]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, eval_mul, eval_pow, eval_X]
    ring

theorem isRoot_charpoly_latticeHecke (hpN : ¬ p ∣ N) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (periodLattice N))
    (hspan : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) :
      Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) = ⊤)
    (h : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hh : h.IsNormalizedEigenform) :
    (((@LinearMap.charpoly ℤ (periodLattice N) _ _ _ (Module.Free.of_basis b)
        (Module.Finite.of_basis b) (latticeHecke N hp))).map (Int.castRingHom ℂ)).IsRoot
      (ModularFormClass.qCoeff h p) := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  set χ := (latticeHecke N hp).charpoly with hχ
  set c : ℂ := (χ.map (Int.castRingHom ℂ)).eval (ModularFormClass.qCoeff h p) with hc

  have hCH : aeval (latticeHecke N hp) χ = 0 := LinearMap.aeval_self_charpoly _
  have hvan : ∀ x : periodLattice N, c * (x : Module.Dual ℂ _) h = 0 := by
    intro x
    rw [hc, ← coe_aeval_latticeHecke_apply_eval N hp hpN χ x h hh, hCH, LinearMap.zero_apply,
      Submodule.coe_zero, LinearMap.zero_apply]
  by_contra hne
  have hne' : c ≠ 0 := hne

  have hall : ∀ φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2), φ h = 0 := by
    intro φ
    have hφ : φ ∈ Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) :
        Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) := by
      rw [hspan]; exact Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact (mul_eq_zero.mp (hvan (b i))).resolve_left hne'
    | zero => rfl
    | add y z _ _ hy hz => rw [LinearMap.add_apply, hy, hz, add_zero]
    | smul r y _ hy => rw [LinearMap.smul_apply, hy, smul_zero]
  have h0 : h = 0 := (Module.forall_dual_apply_eq_zero_iff ℂ h).mp hall
  exact ne_zero_of_isNormalizedEigenform hh h0

end Lattice

section LinearAlgebra

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

theorem exists_ne_zero_apply_eq_smul_of_eval_charpoly (φ : Module.End R M) (k : R)
    (hk : φ.charpoly.eval k = 0) : ∃ v : M, v ≠ 0 ∧ φ v = k • v := by
  rw [LinearMap.eval_charpoly] at hk
  have hlt := LinearMap.bot_lt_ker_of_det_eq_zero hk
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hlt.ne'
  refine ⟨v, hv0, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hv
  exact hv.symm

theorem det_eq_zero_of_forall_apply_apply_eq_zero (φ : M →ₗ[R] R) (G : Module.End R M)
    (h : ∀ y, φ (G y) = 0) (y₀ : M) (hy₀ : φ y₀ ≠ 0) : LinearMap.det G = 0 := by
  classical
  let b := Module.finBasis R M
  set A := LinearMap.toMatrix b b G with hA
  let adj : Module.End R M := Matrix.toLin b b A.adjugate
  have hcomp : ∀ y, G (adj y) = LinearMap.det G • y := by
    intro y
    have h1 : Matrix.toLin b b (A * A.adjugate) y = G (adj y) := by
      rw [Matrix.toLin_mul_apply b b b, hA, Matrix.toLin_toMatrix]
    rw [← h1, Matrix.mul_adjugate, LinearEquiv.map_smul, Matrix.toLin_one, LinearMap.smul_apply,
      LinearMap.id_apply, hA, LinearMap.det_toMatrix]
  have h2 : LinearMap.det G * φ y₀ = 0 := by
    have := h (adj y₀)
    rwa [hcomp, map_smul, smul_eq_mul] at this
  exact (mul_eq_zero.mp h2).resolve_right hy₀

theorem exists_ne_zero_apply_eq_zero_of_forall_apply_apply_eq_zero (φ : M →ₗ[R] R)
    (G : Module.End R M) (h : ∀ y, φ (G y) = 0) (y₀ : M) (hy₀ : φ y₀ ≠ 0) :
    ∃ v : M, v ≠ 0 ∧ G v = 0 := by
  have hdet := det_eq_zero_of_forall_apply_apply_eq_zero φ G h y₀ hy₀
  have hlt := LinearMap.bot_lt_ker_of_det_eq_zero hdet
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hlt.ne'
  exact ⟨v, hv0, hv⟩

theorem charpoly_eq_of_intertwining {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Free R M] [Module.Finite R M]
    [Module.Free R M'] [Module.Finite R M']
    (e : M ≃ₗ[R] M') (T : Module.End R M) (T₀ : Module.End R M') (he : ∀ x, e (T x) = T₀ (e x)) :
    T.charpoly = T₀.charpoly := by
  have hconj : e.conj T = T₀ := by
    apply LinearMap.ext
    intro y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, he, LinearEquiv.apply_symm_apply]
  rw [← hconj, LinearEquiv.charpoly_conj]

end LinearAlgebra

section Cyclotomic

theorem cyclotomicCharacter_frobenius (r p : ℕ) [Fact r.Prime] (hp : p.Prime) (hrp : r ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ p) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) r σ.toRingEquiv : ℤ_[r]ˣ) : ℤ_[r]) = (p : ℤ_[r]) := by
  have hr : r.Prime := Fact.out
  haveI : NeZero ((r : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hr.ne_zero⟩
  refine PadicInt.ext_of_toZModPow.mp (fun n => ?_)
  have hn : Nat.card (rootsOfUnity (r ^ n) (AlgebraicClosure ℚ)) = r ^ n :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) (r ^ n)
  have h1 : PadicInt.toZModPow n
      ((cyclotomicCharacter (AlgebraicClosure ℚ) r σ.toRingEquiv : ℤ_[r]ˣ) : ℤ_[r]) =
        ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn σ.toRingEquiv : (ZMod (r ^ n))ˣ) :
          ZMod (r ^ n)) :=
    cyclotomicCharacter.toZModPow r σ.toRingEquiv
  rw [h1, map_natCast]
  have hcop : (r ^ n).Coprime p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes hr hp).mpr hrp)
  refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ) hn σ.toRingEquiv
    (c := (p : ZMod (r ^ n))) ?_).symm
  intro t ht
  have ht' : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ (r ^ n) = 1 := by
    rw [mem_rootsOfUnity] at ht
    have := congrArg Units.val ht
    simpa using this
  have hfrob := ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ p (r ^ n) hA hσ hcop
    ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ht'
  rw [ZMod.val_natCast, ← pow_eq_pow_mod p ht']
  exact hfrob

end Cyclotomic

section Glue

open ModularCurve AlgebraicCurve

theorem adjoin_preimage_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] (S : Set L) :
    IntermediateField.adjoin K
        (((↑) : IntermediateField.adjoin K S → L) ⁻¹' S) = ⊤ := by
  apply IntermediateField.lift_injective
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_preimage_eq_of_subset]
  intro x hx
  exact ⟨⟨x, IntermediateField.subset_adjoin K S hx⟩, rfl⟩

theorem divisorExpansionsC_finite (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    (divisorExpansionsC k N).Finite := by
  classical
  refine (Set.Finite.image (fun d : ℕ => if h : d = 0 then (0 : LaurentSeries k) else
      (haveI : NeZero d := ⟨h⟩; qExpand k d (jqModC k))) (N.divisors.finite_toSet)).subset ?_
  rintro x ⟨d, hne, hdvd, rfl⟩
  refine ⟨d, Nat.mem_divisors.2 ⟨hdvd, NeZero.ne N⟩, ?_⟩
  simp only [dif_neg hne.ne]

theorem exists_finset_adjoin_eq_top (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    ∃ s : Finset (modularFunctionFieldFullC k N),
      IntermediateField.adjoin k (s : Set (modularFunctionFieldFullC k N)) = ⊤ := by
  have hfin : (((↑) : modularFunctionFieldFullC k N → LaurentSeries k) ⁻¹'
      divisorExpansionsC k N).Finite :=
    (divisorExpansionsC_finite k N).preimage Subtype.val_injective.injOn
  refine ⟨hfin.toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact adjoin_preimage_eq_top (divisorExpansionsC k N)

section BaseChange

variable (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ)

abbrev cst : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K

theorem coeffMap_cst_mem {x : LaurentSeries (ZMod ℓ)}
    (hx : x ∈ modularFunctionFieldFullC (ZMod ℓ) N) :
    coeffMap (cst K ℓ) x ∈ modularFunctionFieldFullC K N := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hne, hdvd, rfl⟩ := hy
    haveI := hne
    rw [coeffMap_qExpand, coeffMap_jqModC]
    exact jqModCd_mem_full K N hdvd
  | algebraMap c =>
    rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (modularFunctionFieldFullC K N).algebraMap_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | inv y _ hy => rw [map_inv₀]; exact inv_mem hy
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

private def _root_.CuspForm.NoEigenvalueOneAddPrime.baseChange : modularFunctionFieldFullC (ZMod ℓ) N →+* modularFunctionFieldFullC K N where
  toFun x := ⟨coeffMap (cst K ℓ) (x : LaurentSeries (ZMod ℓ)), coeffMap_cst_mem K ℓ N x.2⟩
  map_one' := Subtype.ext (map_one (coeffMap (cst K ℓ)))
  map_mul' _ _ := Subtype.ext (map_mul (coeffMap (cst K ℓ)) _ _)
  map_zero' := Subtype.ext (map_zero (coeffMap (cst K ℓ)))
  map_add' _ _ := Subtype.ext (map_add (coeffMap (cst K ℓ)) _ _)

p2m_export "CuspForm.NoEigenvalueOneAddPrime" "baseChange"
@[scoped simp]
theorem coe_baseChange (x : modularFunctionFieldFullC (ZMod ℓ) N) :
    (baseChange K ℓ N x : LaurentSeries K) = coeffMap (cst K ℓ) x := rfl

theorem frobeniusModL_baseChange (x : modularFunctionFieldFullC (ZMod ℓ) N) :
    frobeniusModL K N ℓ (baseChange K ℓ N x) = baseChange K ℓ N (x ^ ℓ) := by
  apply Subtype.ext
  rw [coe_frobeniusModL, coe_baseChange, coe_baseChange, ← coeffMap_qExpand]
  congr 1
  push_cast
  exact (pow_char_eq_qExpand_of_coeff_fixed ℓ (x : LaurentSeries (ZMod ℓ))
    (fun k => ZMod.pow_card _)).symm

theorem adjoin_range_baseChange_eq_top [NeZero N] :
    IntermediateField.adjoin K (Set.range (baseChange K ℓ N)) = ⊤ := by
  refine top_le_iff.mp ((adjoin_preimage_eq_top (K := K) (divisorExpansionsC K N)).ge.trans
    (IntermediateField.adjoin.mono _ _ _ ?_))
  rintro x (hx : (x : LaurentSeries K) ∈ divisorExpansionsC K N)
  obtain ⟨d, hne, hdvd, hxd⟩ := hx
  haveI := hne
  refine ⟨⟨qExpand (ZMod ℓ) d (jqModC (ZMod ℓ)), jqModCd_mem_full (ZMod ℓ) N hdvd⟩, Subtype.ext ?_⟩
  rw [coe_baseChange, hxd]
  push_cast
  rw [coeffMap_qExpand, coeffMap_jqModC]

end BaseChange

theorem finite_fixedPoints_frobeniusPushforwardModL_iterate
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (halg : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ ℓ ^ n = a)
    (N : ℕ) [NeZero N] (j : ℕ) (hj : 0 < j) :
    (Function.fixedPoints (frobeniusPushforwardModL K N ℓ)^[j]).Finite := by
  classical
  letI : Algebra (modularFunctionFieldFullC (ZMod ℓ) N) (modularFunctionFieldFullC K N) :=
    (baseChange K ℓ N).toAlgebra
  haveI : IsCurveOver (ZMod ℓ) (modularFunctionFieldFullC (ZMod ℓ) N) :=
    isCurveOver_modularFunctionFieldFullC (ZMod ℓ) N
  haveI : IsCurveOver K (modularFunctionFieldFullC K N) := isCurveOver_modularFunctionFieldFullC K N
  have hq : Nat.card (ZMod ℓ) = ℓ := Nat.card_zmod ℓ
  have hφ : ∀ x : modularFunctionFieldFullC (ZMod ℓ) N,
      frobeniusModL K N ℓ (algebraMap _ _ x) = algebraMap _ _ (x ^ Nat.card (ZMod ℓ)) := by
    intro x
    rw [hq]
    exact frobeniusModL_baseChange K ℓ N x
  have hgen : IntermediateField.adjoin K
      (Set.range (algebraMap (modularFunctionFieldFullC (ZMod ℓ) N)
        (modularFunctionFieldFullC K N))) = ⊤ :=
    adjoin_range_baseChange_eq_top K ℓ N
  have hfg := exists_finset_adjoin_eq_top (ZMod ℓ) N
  haveI : Algebra.EssFiniteType (ZMod ℓ) (modularFunctionFieldFullC (ZMod ℓ) N) := by
    obtain ⟨s, hs⟩ := hfg
    exact IntermediateField.fg_top_iff.mp ⟨s, hs⟩
  have hC : ConstantsAreBase (ZMod ℓ) (modularFunctionFieldFullC (ZMod ℓ) N) :=
    constantsAreBase_of_deg_eq_one (qInftyPlaceMod (ZMod ℓ) (jqModC_mem_full (ZMod ℓ) N))
      (deg_qInftyPlaceMod (ZMod ℓ) (jqModC_mem_full (ZMod ℓ) N))
  have halg' : ∀ a : K, ∃ n : ℕ, 0 < n ∧ a ^ Nat.card (ZMod ℓ) ^ n = a := by
    rw [hq]; exact halg

  obtain ⟨_, hfin, hFI, hN'⟩ := ModularCurve.frobeniusInputsModL K N (ℓ := ℓ)
  have hT : ∀ D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N),
      frobeniusPushforwardModL K N ℓ (Pic0.mk D) =
        Pic0.mk ⟨Divisor.pushforwardAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) D,
          Divisor.pushforwardAlong_mem_degZero (frobeniusModL K N ℓ)
            (frobeniusModL_isIntegral K N ℓ) D.2⟩ := by
    intro D
    rw [frobeniusPushforwardModL_mk hfin hFI hN']
    rfl
  obtain ⟨P, -, -, -, -, hfix⟩ :=
    AlgebraicCurve.Pic0.exists_monic_natCard_fixedPoints_iterate_eq_resultant_of_pushforwardAlong_frobenius
      (ZMod ℓ) K (modularFunctionFieldFullC (ZMod ℓ) N) (modularFunctionFieldFullC K N)
      hfg hC hgen halg' (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) hφ
      (frobeniusPushforwardModL K N ℓ) hT
  exact (hfix j hj).1

section Levels

variable {r : ℕ} {M : Type} [AddCommGroup M]

theorem level_eq_pow_smul (x : TateModule r M) {n m : ℕ} (h : n ≤ m) :
    (x : ℕ → M) n = ((r ^ (m - n) : ℕ) : ℤ) • (x : ℕ → M) m := by
  have := TateModule.compat_pow x n (m - n)
  rw [Nat.add_sub_cancel' h] at this
  exact this.symm

theorem eq_zero_of_pow_smul_eq_self {y : M} {L d : ℕ} (hd : 0 < d)
    (hL : ((r ^ L : ℕ) : ℤ) • y = 0) (hy : ((r ^ d : ℕ) : ℤ) • y = y) : y = 0 := by
  have hk : ∀ k : ℕ, ((r ^ (d * k) : ℕ) : ℤ) • y = y := by
    intro k
    induction k with
    | zero => rw [mul_zero, pow_zero, Nat.cast_one, one_smul]
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, Nat.cast_mul, mul_smul, hy, ih]
  have hle : L ≤ d * L := Nat.le_mul_of_pos_left L hd
  have := hk L
  rw [← Nat.sub_add_cancel hle, pow_add, Nat.cast_mul, mul_smul, hL, smul_zero] at this
  exact this.symm

theorem level_injective_of_ne_zero (x : TateModule r M) {n₀ : ℕ} (hx : (x : ℕ → M) n₀ ≠ 0)
    (hr : 1 < r) : Function.Injective fun n : ℕ => (x : ℕ → M) (n₀ + n) := by
  have key : ∀ a b : ℕ, a < b → (x : ℕ → M) (n₀ + a) = (x : ℕ → M) (n₀ + b) → False := by
    intro a b hab heq
    have h1 := level_eq_pow_smul x (Nat.add_le_add_left hab.le n₀)
    rw [Nat.add_sub_add_left] at h1

    have hy : (x : ℕ → M) (n₀ + b) = 0 :=
      eq_zero_of_pow_smul_eq_self (Nat.sub_pos_of_lt hab) (TateModule.torsion x (n₀ + b))
        (h1.symm.trans heq)
    apply hx
    rw [level_eq_pow_smul x (Nat.le_add_right n₀ b), hy, smul_zero]
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact (key a b h hab).elim
  · exact h
  · exact (key b a h hab.symm).elim

end Levels

theorem tateModule_eq_zero_of_rep_pow_eq (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) {r : ℕ} [Fact r.Prime] (hrp : r ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ p)
    (j : ℕ) (hj : 0 < j) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ = σ ^ j)
    (t : TateModule r (JZero N))
    (ht : TateModule.rep r (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ t = t) :
    t = 0 := by
  classical
  subst hτ
  have hr : r.Prime := Fact.out
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra ht0

  have hex : ∃ n₀, (t : ℕ → JZero N) n₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ht0 (Subtype.ext (funext fun n => by rw [hall n]; rfl))
  obtain ⟨n₀, hn₀⟩ := hex

  haveI : CharP (IsLocalRing.ResidueField A) p :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def hp hA
  have hred : ReductionInputsModL A N := reductionInputsModL_of_not_dvd N hpN A hA
  have halg : ∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ p ^ n = a :=
    fun a => ValuationSubring.exists_pow_pow_eq_self_residueField_of_liesOverPrime A hp hA a

  have hFr : ∀ (k : ℕ) (z : JZero N), reductionModL A N ((σ ^ k) • z) =
      (frobeniusPushforwardModL (IsLocalRing.ResidueField A) N p)^[k] (reductionModL A N z) := by
    intro k
    induction k with
    | zero => intro z; rw [pow_zero, one_smul, Function.iterate_zero, id]
    | succ k ih =>
      intro z
      rw [pow_succ, mul_smul, ih, reductionModL_smul_of_isFrobeniusAt N A hred σ hσ z,
        ← Function.iterate_succ_apply]

  have hlev : ∀ n, (σ ^ j) • (t : ℕ → JZero N) n = (t : ℕ → JZero N) n := by
    intro n
    have := congrArg (fun z : TateModule r (JZero N) => (z : ℕ → JZero N) n) ht
    simpa only [TateModule.rep_apply] using this
  have hmem : ∀ n, reductionModL A N ((t : ℕ → JZero N) n) ∈
      Function.fixedPoints (frobeniusPushforwardModL (IsLocalRing.ResidueField A) N p)^[j] := by
    intro n
    rw [Function.mem_fixedPoints, Function.IsFixedPt, ← hFr j, hlev n]

  have hinj : Function.Injective fun n : ℕ => reductionModL A N ((t : ℕ → JZero N) (n₀ + n)) := by
    intro a b hab
    apply level_injective_of_ne_zero t hn₀ hr.one_lt

    have hsub : reductionModL A N ((t : ℕ → JZero N) (n₀ + a) - (t : ℕ → JZero N) (n₀ + b)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hab
    have htor : (r ^ (n₀ + a + (n₀ + b))) •
        ((t : ℕ → JZero N) (n₀ + a) - (t : ℕ → JZero N) (n₀ + b)) = 0 := by
      rw [nsmul_sub, ← natCast_zsmul, ← natCast_zsmul]
      have ha : ((r ^ (n₀ + a + (n₀ + b)) : ℕ) : ℤ) • (t : ℕ → JZero N) (n₀ + a) = 0 := by
        rw [pow_add, Nat.cast_mul, mul_comm, mul_smul, TateModule.torsion, smul_zero]
      have hb : ((r ^ (n₀ + a + (n₀ + b)) : ℕ) : ℤ) • (t : ℕ → JZero N) (n₀ + b) = 0 := by
        rw [pow_add, Nat.cast_mul, mul_smul, TateModule.torsion, smul_zero]
      rw [ha, hb, sub_zero]
    have hpm : ¬ p ∣ r ^ (n₀ + a + (n₀ + b)) := fun h =>
      hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)).symm
    have := eq_zero_of_reductionModL_eq_zero_of_nsmul_eq_zero N hpN A hA hred _ hpm _ htor hsub
    exact sub_eq_zero.mp this

  have hfin := finite_fixedPoints_frobeniusPushforwardModL_iterate (IsLocalRing.ResidueField A) p
    halg N j hj
  have hinf : (Set.range fun n : ℕ => reductionModL A N ((t : ℕ → JZero N) (n₀ + n))).Infinite :=
    Set.infinite_range_of_injective hinj
  exact hinf (hfin.subset (by rintro _ ⟨n, rfl⟩; exact hmem (n₀ + n)))

end Glue

section EichlerShimuraAlgebra

variable {R T : Type*} [CommRing R] [AddCommGroup T] [Module R T]

theorem exists_frobenius_eigenvector (F Finv Tp : Module.End R T) (p : ℕ) (ε : ℤ)
    (hε : ε * ε = 1)
    (hES : ∀ x, F (F x) - Tp (F x) + p • x = 0)
    (hinv : ∀ x, F (Finv x) = x)
    (t₀ : T) (ht₀ : t₀ ≠ 0) (hTp : Tp t₀ = (ε * (1 + p) : ℤ) • t₀) :
    ∃ w : T, w ≠ 0 ∧ (F w = ε • w ∨ F w = (ε * p : ℤ) • w) := by
  set w := Finv t₀ with hw
  have hFw : F w = t₀ := hinv t₀
  have hw0 : w ≠ 0 := by
    intro h0
    apply ht₀
    rw [← hFw, h0, map_zero]

  have hFt : F t₀ = (ε * (1 + p) : ℤ) • t₀ - (p : ℤ) • w := by
    have := hES w
    rw [hFw, hTp, ← natCast_zsmul, sub_add_eq_add_sub, sub_eq_zero] at this
    exact eq_sub_of_add_eq this
  set u := t₀ - (ε * p : ℤ) • w with hu
  have hFu : F u = ε • u := by
    rw [hu, map_sub, map_zsmul, hFw, hFt, smul_sub, smul_smul, ← mul_assoc, hε, one_mul]
    module
  by_cases hu0 : u = 0
  · refine ⟨w, hw0, Or.inr ?_⟩
    rw [hFw]
    exact (sub_eq_zero.mp hu0)
  · exact ⟨u, hu0, Or.inl hFu⟩

end EichlerShimuraAlgebra

section Assembly

open ModularCurve

theorem exists_prime_ne (p : ℕ) : ∃ q : ℕ, q.Prime ∧ q ≠ p := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (p + 1)
  exact ⟨q, hqp, by omega⟩

theorem exists_sign_of_sq_eq {a b : ℂ} (h : a ^ 2 = b ^ 2) :
    ∃ ε : ℤ, ε * ε = 1 ∧ a = ε * b := by
  have h' : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact ⟨1, by norm_num, by push_cast; linear_combination h1⟩
  · exact ⟨-1, by norm_num, by push_cast; linear_combination h1⟩

theorem main (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (h : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hh : h.IsNormalizedEigenform)
    (hsq : ModularFormClass.qCoeff h p ^ 2 = ((1 : ℂ) + p) ^ 2) : False := by
  classical
  letI := ModularCurve.heckeModuleBar N

  obtain ⟨ε, hε, ha⟩ := exists_sign_of_sq_eq hsq
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = ε * (1 + p) := ⟨_, rfl⟩
  have hak : ModularFormClass.qCoeff h p = (k : ℂ) := by rw [ha, hk]; push_cast; ring

  obtain ⟨r, hr, hrp⟩ := exists_prime_ne p
  haveI : Fact r.Prime := ⟨hr⟩
  have hpNr : ¬ p ∣ N * r := by
    intro hdiv
    rcases (Nat.Prime.dvd_mul hp).mp hdiv with h1 | h2
    · exact hpN h1
    · exact hrp (((Nat.prime_dvd_prime_iff_eq hp hr).mp h2)).symm
  obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat p hp

  obtain ⟨n, b, -, hspan⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  obtain ⟨e, he⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
      N r (ModularCurve.heckeInputsAll N) (ModularCurve.heckeOperatorsCommuteBar N)
      (ModularCurve.periodLatticeHeckeStable N)

  let bT : Module.Basis (Fin n) ℤ_[r] (TateModule r (JZero N)) :=
    (Algebra.TensorProduct.basis ℤ_[r] b).map e.symm
  haveI : Module.Free ℤ_[r] (TateModule r (JZero N)) := Module.Free.of_basis bT
  haveI : Module.Finite ℤ_[r] (TateModule r (JZero N)) := Module.Finite.of_basis bT

  obtain ⟨Tp, hTp⟩ : ∃ Tp : Module.End ℤ_[r] (TateModule r (JZero N)),
      Tp = TateModule.rep r (JZero N) HeckeAlg (heckeGen ⟨p, hp⟩) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Module.End ℤ_[r] (TateModule r (JZero N)),
      F = TateModule.rep r (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ := ⟨_, rfl⟩
  obtain ⟨Finv, hFinv⟩ : ∃ Finv : Module.End ℤ_[r] (TateModule r (JZero N)),
      Finv = TateModule.rep r (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ⁻¹ :=
    ⟨_, rfl⟩
  have hinv : ∀ x, F (Finv x) = x := by
    intro x
    rw [hF, hFinv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hσ2 : σ * σ = σ ^ 2 := (pow_two σ).symm
  have hF2 : ∀ x, F (F x) =
      TateModule.rep r (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (σ * σ) x := by
    intro x
    rw [hF, ← Module.End.mul_apply, ← map_mul]
    try rfl

  have hES : ∀ x : TateModule r (JZero N), F (F x) - Tp (F x) + p • x = 0 := by
    intro x
    rw [hF, hTp]
    exact ModularCurve.frobeniusQuadratic_tateModule_jZero N r
      (ModularCurve.heckeOperatorsCommuteBar N) hp hpNr A hA σ hσ x

  have hroot := isRoot_charpoly_latticeHecke N hp hpN b hspan h hh
  rw [hak, Polynomial.IsRoot.def, Polynomial.eval_intCast_map, eq_intCast, Int.cast_eq_zero] at hroot

  have he' : ∀ x : TateModule r (JZero N),
      e (Tp x) = ((latticeHecke N hp).baseChange ℤ_[r]) (e x) := by
    intro x
    rw [hTp, ← ModularCurve.tateHeckeRep_apply]
    exact he (heckeGen ⟨p, hp⟩) x
  have hchar : Tp.charpoly = ((latticeHecke N hp).charpoly).map (algebraMap ℤ ℤ_[r]) := by
    rw [charpoly_eq_of_intertwining e Tp ((latticeHecke N hp).baseChange ℤ_[r]) he',
      LinearMap.charpoly_baseChange]
  have hevalT : Tp.charpoly.eval (k : ℤ_[r]) = 0 := by
    rw [hchar, show (algebraMap ℤ ℤ_[r]) = Int.castRingHom ℤ_[r] from RingHom.ext_int _ _,
      Polynomial.eval_intCast_map, hroot, map_zero]

  obtain ⟨t₀, ht₀, hTpt₀⟩ := exists_ne_zero_apply_eq_smul_of_eval_charpoly Tp (k : ℤ_[r]) hevalT
  rw [Int.cast_smul_eq_zsmul, hk] at hTpt₀

  obtain ⟨w, hw0, hw⟩ := exists_frobenius_eigenvector F Finv Tp p ε hε hES hinv t₀ ht₀ hTpt₀
  have hεε : ∀ x : TateModule r (JZero N), ε • (ε • x) = x := fun x => by
    rw [smul_smul, hε, one_smul]
  rcases hw with hw1 | hw2
  ·
    have hfix : TateModule.rep r (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (σ * σ) w = w := by
      rw [← hF2, hw1, map_zsmul, hw1, hεε]
    exact hw0 (tateModule_eq_zero_of_rep_pow_eq N hp hpN hrp A hA σ hσ 2 two_pos (σ * σ) hσ2 w hfix)
  ·
    obtain ⟨B, hBσ, hBleft, -⟩ :=
      ModularCurve.JZero.exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul r N
    have hχ := cyclotomicCharacter_frobenius r p hp hrp A hA σ hσ
    have hεr : (ε : ℤ_[r]) * (ε : ℤ_[r]) = 1 := by exact_mod_cast hε
    have hw2' : F w = ((ε * p : ℤ) : ℤ_[r]) • w := by
      rw [hw2]; exact (Int.cast_smul_eq_zsmul ℤ_[r] _ w).symm

    have hstep : ∀ y : TateModule r (JZero N), B w (F y) = (ε : ℤ_[r]) * B w y := by
      intro y
      have h1 := hBσ σ w y
      rw [hχ, ← hF, hw2', map_smul, LinearMap.smul_apply, smul_eq_mul] at h1

      have h2 : (p : ℤ_[r]) * B w (F y) = (p : ℤ_[r]) * ((ε : ℤ_[r]) * B w y) := by
        have h3 := congrArg (fun z : ℤ_[r] => (ε : ℤ_[r]) * z) h1
        simp only [Int.cast_mul, Int.cast_natCast] at h3
        calc (p : ℤ_[r]) * B w (F y)
            = ((ε : ℤ_[r]) * (ε : ℤ_[r])) * ((p : ℤ_[r]) * B w (F y)) := by rw [hεr, one_mul]
          _ = (ε : ℤ_[r]) * ((ε : ℤ_[r]) * (p : ℤ_[r]) * B w (F y)) := by ring
          _ = (ε : ℤ_[r]) * ((p : ℤ_[r]) * B w y) := by rw [h3]
          _ = (p : ℤ_[r]) * ((ε : ℤ_[r]) * B w y) := by ring
      have hp0 : (p : ℤ_[r]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      exact mul_left_cancel₀ hp0 h2

    have hkill : ∀ y : TateModule r (JZero N), B w ((F * F - 1) y) = 0 := by
      intro y
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, map_sub, hstep, hstep,
        ← mul_assoc, hεr, one_mul, sub_self]

    have hy₀ : ∃ y₀ : TateModule r (JZero N), B w y₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0 (hBleft w hall)
    obtain ⟨y₀, hy₀⟩ := hy₀
    obtain ⟨v, hv0, hv⟩ :=
      exists_ne_zero_apply_eq_zero_of_forall_apply_apply_eq_zero (B w) (F * F - 1) hkill y₀ hy₀
    have hfix : TateModule.rep r (JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (σ * σ) v = v := by
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply, sub_eq_zero] at hv
      rw [← hF2, hv]
    exact hv0 (tateModule_eq_zero_of_rep_pow_eq N hp hpN hrp A hA σ hσ 2 two_pos (σ * σ) hσ2 v hfix)

end Assembly

end CuspForm.NoEigenvalueOneAddPrime
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform.CuspForm P2MW.S_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform.CuspForm.NoEigenvalueOneAddPrime"
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform.CuspForm"

end
p2m_reactivate "P2MW.S_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform.CuspForm P2MW.S_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform.CuspForm.NoEigenvalueOneAddPrime"

theorem solution
    (N₀ p : ℕ) (hp : p.Prime) (hpN₀ : ¬ p ∣ N₀)
    (h : CuspForm (CongruenceSubgroup.Gamma0 N₀) 2) (hh : h.IsNormalizedEigenform) :
    ModularFormClass.qCoeff h p ^ 2 ≠ ((1 : ℂ) + p) ^ 2 := by
  haveI : NeZero N₀ := ⟨by rintro rfl; exact hpN₀ (dvd_zero p)⟩
  exact fun hsq => CuspForm.NoEigenvalueOneAddPrime.main N₀ p hp hpN₀ h hh hsq

end S_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform
end P2MW
export P2MW.S_CuspForm_qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform (solution)

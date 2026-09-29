-- Prove2me | solution 1 for CuspForm.TWLevel.HeckeRing.exists_finiteLevel_surjective_pi_torsion_jH_levelQuotient_of_not_dvd_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6704fed9-307a-522f-996a-919df8c8d00f

import Mathlib
import Definitions.Def_CuspForm_TWLevelHeckeRing
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level
import Theorems.Thm_GaloisRepAdic_exists_quadraticRelation_forall_of_frobenius
import Theorems.Thm_Representation_exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced
import Theorems.Thm_CuspForm_TWLevel_HeckeRing_isReduced
import Theorems.Thm_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete
import Theorems.Thm_GaloisRepAdic_span_range_eq_top_of_residual_isAbsolutelyIrreducible
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_surjective_pi_torsion_jH_levelQuotient_of_not_dvd_level
p2m_attr_erase "instance" "IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par CohCarrier.GammaHLower_finiteIndex AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_apply IharaLemma.IdempotentSplitting.cornerRingLinearEquiv_symm_apply IharaLemma.IdempotentSplitting.coe_cornerSmul IharaLemma.IdempotentSplitting.mk.injEq IharaLemma.IdempotentSplitting.mk.sizeOf_spec IharaLemma.IdempotentSplitting.coe_toCornerRing IharaLemma.toCorner_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_laurentReductionDegZero ModularCurve.laurentReductionDiv_apply ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply"
p2m_attr_erase "simp" "CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

open IsLocalRing

namespace R1RealPrimeAsm

theorem residual_isAbsolutelyIrreducible_of_equiv {k : Type} [Field k]
    {ρ₁ ρ₂ : ResidualGaloisRep k} (e : ResidualGaloisRep.Equiv ρ₁ ρ₂)
    (h : ρ₂.IsAbsolutelyIrreducible) : ρ₁.IsAbsolutelyIrreducible := by
  refine ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
    ρ₂ ρ₁ h fun σ => ?_
  have hconj : ρ₂.ρ σ = e.toLinearEquiv.conj (ρ₁.ρ σ) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply, e.map_apply, LinearEquiv.apply_symm_apply]
  rw [hconj, LinearEquiv.charpoly_conj]

theorem exists_pow_mem_of_finite_quotient {T : Type} [CommRing T] [IsLocalRing T]
    (x : T) (hx : x ∈ maximalIdeal T) (I : Ideal T) (hI : Finite (T ⧸ I)) :
    ∃ c : ℕ, x ^ c ∈ I := by
  classical
  by_cases hIt : I = ⊤
  · exact ⟨0, by rw [hIt]; exact Submodule.mem_top⟩
  haveI : Nontrivial (T ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIt
  haveI : IsLocalRing (T ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsArtinianRing (T ⧸ I) := isArtinian_of_finite

  have hxbar : Ideal.Quotient.mk I x ∈ maximalIdeal (T ⧸ I) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨u, hu⟩ := hu
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : T ⧸ I)
    have h1 : Ideal.Quotient.mk I (x * y - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hy, ← hu, Units.mul_inv, sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 : x * y - 1 ∈ maximalIdeal T := IsLocalRing.le_maximalIdeal hIt h1
    have h3 : x * y ∈ maximalIdeal T := Ideal.mul_mem_right y _ hx
    have h4 : (1 : T) ∈ maximalIdeal T := by
      have := Ideal.sub_mem _ h3 h2
      rwa [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal T).ne_top ((Ideal.eq_top_iff_one _).mpr h4)
  obtain ⟨c, hc⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T ⧸ I)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hc
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  have : Ideal.Quotient.mk I x ^ c ∈ (maximalIdeal (T ⧸ I)) ^ c := Ideal.pow_mem_pow hxbar c
  rw [hc] at this
  exact (Submodule.mem_bot _).mp this

section Lattice

open Submodule

variable {R : Type*} [CommRing R]

theorem exists_inf_pow_smul_le [IsNoetherianRing R] {Y : Type*} [AddCommGroup Y] [Module R Y]
    [Module.Finite R Y] (p : R) (N : Submodule R Y) (c : ℕ) :
    ∃ m : ℕ, N ⊓ (Ideal.span {p} ^ m • ⊤ : Submodule R Y) ≤ Ideal.span {p} ^ c • N := by
  obtain ⟨k, hk⟩ := (Ideal.span {p} : Ideal R).exists_pow_inf_eq_pow_smul N
  refine ⟨k + c, ?_⟩
  rw [inf_comm, hk (k + c) (Nat.le_add_right k c), Nat.add_sub_cancel_left]
  exact Submodule.smul_mono le_rfl inf_le_right

variable {G : Type*} [Monoid G]

theorem exists_stable_submodule_surjective_equivariant [IsNoetherianRing R]
    {V Y : Type*} [AddCommGroup V] [Module R V] [AddCommGroup Y] [Module R Y] [Module.Finite R Y]
    (πV : G →* Module.End R V) (πY : G →* Module.End R Y)
    (j : V →ₗ[R] Y) (hj : Function.Injective j) (hjG : ∀ g v, j (πV g v) = πY g (j v))
    (p : R) (c : ℕ) :
    ∃ (m : ℕ) (X : Submodule R (Y ⧸ (Ideal.span {p} ^ m • ⊤ : Submodule R Y)))
      (hX : ∀ (g : G) (x : Y), Submodule.Quotient.mk x ∈ X → Submodule.Quotient.mk (πY g x) ∈ X)
      (π : X →ₗ[R] V ⧸ (Ideal.span {p} ^ c • ⊤ : Submodule R V)),
      Function.Surjective π ∧
      ∀ (g : G) (x : Y) (hx : Submodule.Quotient.mk x ∈ X),
        π ⟨Submodule.Quotient.mk (πY g x), hX g x hx⟩ =
          Submodule.mapQ _ _ (πV g) (by
            rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
            exact Submodule.smul_mono le_rfl le_top) (π ⟨Submodule.Quotient.mk x, hx⟩) := by
  classical
  set N : Submodule R Y := LinearMap.range j with hN
  obtain ⟨m, hm⟩ := exists_inf_pow_smul_le p N c
  set PmY : Submodule R Y := Ideal.span {p} ^ m • ⊤ with hPmY
  set PcV : Submodule R V := Ideal.span {p} ^ c • ⊤ with hPcV

  let X : Submodule R (Y ⧸ PmY) := N.map PmY.mkQ

  have hkey : ∀ v : V, j v ∈ PmY → v ∈ PcV := by
    intro v hv
    have hmem : j v ∈ N ⊓ PmY := ⟨LinearMap.mem_range_self j v, hv⟩
    have h2 : j v ∈ Ideal.span {p} ^ c • N := hm hmem

    have h3 : Ideal.span {p} ^ c • N = (Ideal.span {p} ^ c • (⊤ : Submodule R V)).map j := by
      rw [hN, ← Submodule.map_top, Submodule.map_smul'']
    rw [h3] at h2
    obtain ⟨w, hw, hjw⟩ := h2
    have : w = v := hj hjw
    rw [← this]; exact hw

  have hpre : ∀ y : N, ∃ v : V, j v = y := fun y => by
    obtain ⟨v, hv⟩ := y.2; exact ⟨v, hv⟩
  let lift : N → V := fun y => (hpre y).choose
  have hlift : ∀ y : N, j (lift y) = y := fun y => (hpre y).choose_spec
  have hlift_eq : ∀ (v : V), lift ⟨j v, LinearMap.mem_range_self j v⟩ = v :=
    fun v => hj (hlift _)
  let φ₀ : N →ₗ[R] V :=
    { toFun := lift
      map_add' := fun x y => hj (by rw [hlift, map_add, hlift, hlift]; rfl)
      map_smul' := fun r x => hj (by rw [hlift, map_smul, hlift]; rfl) }
  have hφ₀ : ∀ v : V, φ₀ ⟨j v, LinearMap.mem_range_self j v⟩ = v := hlift_eq
  let φ : N →ₗ[R] V ⧸ PcV := PcV.mkQ.comp φ₀

  have hφker : ∀ y : N, (y : Y) ∈ PmY → φ y = 0 := by
    intro y hy
    obtain ⟨v, hv⟩ := hpre y
    have : y = ⟨j v, LinearMap.mem_range_self j v⟩ := Subtype.ext hv.symm
    subst this
    show PcV.mkQ (φ₀ ⟨j v, _⟩) = 0
    rw [hφ₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hkey v hy

  have hXmem : ∀ x : X, ∃ y : N, PmY.mkQ (y : Y) = (x : Y ⧸ PmY) := by
    intro x
    obtain ⟨y, hyN, hy⟩ := x.2
    exact ⟨⟨y, hyN⟩, hy⟩
  let ψ : X → V ⧸ PcV := fun x => φ (hXmem x).choose
  have hψ : ∀ (x : X) (y : N), PmY.mkQ (y : Y) = (x : Y ⧸ PmY) → ψ x = φ y := by
    intro x y hy
    have h1 := (hXmem x).choose_spec
    have hdiff : ((hXmem x).choose : Y) - (y : Y) ∈ PmY := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, h1, hy]
    have := hφker ((hXmem x).choose - y) hdiff
    rw [map_sub, sub_eq_zero] at this
    exact this
  let π : X →ₗ[R] V ⧸ PcV :=
    { toFun := ψ
      map_add' := by
        intro a b
        obtain ⟨ya, hya⟩ := hXmem a
        obtain ⟨yb, hyb⟩ := hXmem b
        rw [hψ a ya hya, hψ b yb hyb, hψ (a + b) (ya + yb) (by
          rw [Submodule.coe_add, map_add, hya, hyb]; rfl), map_add]
      map_smul' := by
        intro r a
        obtain ⟨ya, hya⟩ := hXmem a
        rw [hψ a ya hya, hψ (r • a) (r • ya) (by
          rw [Submodule.coe_smul, map_smul, hya]; rfl), map_smul]; rfl }
  have hπj : ∀ v : V, ∀ (hx : PmY.mkQ (j v) ∈ X),
      π ⟨PmY.mkQ (j v), hx⟩ = PcV.mkQ v := by
    intro v hx
    show ψ _ = _
    rw [hψ ⟨PmY.mkQ (j v), hx⟩ ⟨j v, LinearMap.mem_range_self j v⟩ rfl]
    show PcV.mkQ (φ₀ ⟨j v, _⟩) = _
    rw [hφ₀]

  have hXstab : ∀ (g : G) (x : Y), Submodule.Quotient.mk x ∈ X →
      Submodule.Quotient.mk (πY g x) ∈ X := by
    intro g x hx
    obtain ⟨y, hyN, hy⟩ := hx
    obtain ⟨v, rfl⟩ := hyN

    have hdiff : x - j v ∈ PmY := by
      rw [← Submodule.Quotient.eq]; exact hy.symm
    have hpres : ∀ z ∈ PmY, πY g z ∈ PmY := by
      intro z hz
      have : PmY.map (πY g) ≤ PmY := by
        rw [hPmY, Submodule.map_smul'']
        exact Submodule.smul_mono le_rfl le_top
      exact this ⟨z, hz, rfl⟩
    have h1 : Submodule.Quotient.mk (p := PmY) (πY g x) = Submodule.Quotient.mk (πY g (j v)) := by
      rw [Submodule.Quotient.eq, ← map_sub]
      exact hpres _ hdiff
    rw [h1, ← hjG]
    exact ⟨j (πV g v), LinearMap.mem_range_self j _, rfl⟩
  refine ⟨m, X, hXstab, π, ?_, ?_⟩
  ·
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H v =>
      exact ⟨⟨PmY.mkQ (j v), ⟨j v, LinearMap.mem_range_self j v, rfl⟩⟩, hπj v _⟩
  ·
    intro g x hx
    obtain ⟨y, hyN, hy⟩ := id hx
    obtain ⟨v, rfl⟩ := hyN
    have hdiff : x - j v ∈ PmY := by
      rw [← Submodule.Quotient.eq]; exact hy.symm
    have hpres : ∀ z ∈ PmY, πY g z ∈ PmY := by
      intro z hz
      have : PmY.map (πY g) ≤ PmY := by
        rw [hPmY, Submodule.map_smul'']
        exact Submodule.smul_mono le_rfl le_top
      exact this ⟨z, hz, rfl⟩
    have hx' : (Submodule.Quotient.mk x : Y ⧸ PmY) = PmY.mkQ (j v) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]; exact hdiff
    have hgx' : (Submodule.Quotient.mk (πY g x) : Y ⧸ PmY) = PmY.mkQ (j (πV g v)) := by
      rw [hjG, Submodule.mkQ_apply, Submodule.Quotient.eq, ← map_sub]; exact hpres _ hdiff
    have e1 : (⟨Submodule.Quotient.mk (πY g x), hXstab g x hx⟩ : X) =
        ⟨PmY.mkQ (j (πV g v)), ⟨j (πV g v), LinearMap.mem_range_self j _, rfl⟩⟩ :=
      Subtype.ext hgx'
    have e2 : (⟨Submodule.Quotient.mk x, hx⟩ : X) =
        ⟨PmY.mkQ (j v), ⟨j v, LinearMap.mem_range_self j v, rfl⟩⟩ := Subtype.ext hx'
    rw [e1, e2, hπj, hπj]
    rfl

end Lattice

section Transport

variable {R : Type*} [CommRing R] {Y : Type*} [AddCommGroup Y] [Module R Y]
  {T : Type*} [AddCommGroup T] {W : Type*} [AddCommGroup W]

theorem exists_transport (P : Submodule R Y) (ι : Y →+ T) (hι : ∀ y : Y, ι y = 0 ↔ y ∈ P)
    (X : Submodule R (Y ⧸ P)) (π : X →+ W) :
    ∃ (X' : AddSubgroup T) (π' : X' →+ W),
      (∀ x' : T, x' ∈ X' ↔ ∃ y : Y, Submodule.Quotient.mk y ∈ X ∧ ι y = x') ∧
      ∀ (y : Y) (hy : Submodule.Quotient.mk y ∈ X) (hy' : ι y ∈ X'),
        π' ⟨ι y, hy'⟩ = π ⟨Submodule.Quotient.mk y, hy⟩ := by
  classical

  let X' : AddSubgroup T :=
    { carrier := {x' | ∃ y : Y, Submodule.Quotient.mk y ∈ X ∧ ι y = x'}
      add_mem' := by
        rintro a b ⟨ya, hya, rfl⟩ ⟨yb, hyb, rfl⟩
        exact ⟨ya + yb, by rw [Submodule.Quotient.mk_add]; exact X.add_mem hya hyb, map_add ι ya yb⟩
      zero_mem' := ⟨0, by rw [Submodule.Quotient.mk_zero]; exact X.zero_mem, map_zero ι⟩
      neg_mem' := by
        rintro a ⟨ya, hya, rfl⟩
        exact ⟨-ya, by rw [Submodule.Quotient.mk_neg]; exact X.neg_mem hya, map_neg ι ya⟩ }
  have hmem : ∀ x' : X', ∃ y : Y, Submodule.Quotient.mk y ∈ X ∧ ι y = (x' : T) := fun x' => x'.2

  have hwd : ∀ (y₁ y₂ : Y) (h₁ : Submodule.Quotient.mk y₁ ∈ X) (h₂ : Submodule.Quotient.mk y₂ ∈ X),
      ι y₁ = ι y₂ → π ⟨Submodule.Quotient.mk y₁, h₁⟩ = π ⟨Submodule.Quotient.mk y₂, h₂⟩ := by
    intro y₁ y₂ h₁ h₂ he
    have hk : y₁ - y₂ ∈ P := by
      rw [← hι, map_sub, he, sub_self]
    have : (Submodule.Quotient.mk y₁ : Y ⧸ P) = Submodule.Quotient.mk y₂ :=
      (Submodule.Quotient.eq P).mpr hk
    congr 1
    exact Subtype.ext this
  let f : X' → W := fun x' => π ⟨Submodule.Quotient.mk (hmem x').choose, (hmem x').choose_spec.1⟩
  have hf : ∀ (x' : X') (y : Y) (hy : Submodule.Quotient.mk y ∈ X), ι y = (x' : T) →
      f x' = π ⟨Submodule.Quotient.mk y, hy⟩ := by
    intro x' y hy he
    exact hwd _ _ _ _ ((hmem x').choose_spec.2.trans he.symm)
  let π' : X' →+ W :=
    { toFun := f
      map_zero' := by
        have h0 : Submodule.Quotient.mk (p := P) (0 : Y) ∈ X := by
          rw [Submodule.Quotient.mk_zero]; exact X.zero_mem
        rw [hf 0 0 h0 (by rw [map_zero]; rfl)]
        have : (⟨Submodule.Quotient.mk 0, h0⟩ : X) = 0 := Subtype.ext (Submodule.Quotient.mk_zero _)
        rw [this, map_zero]
      map_add' := by
        intro a b
        obtain ⟨ya, hya, hea⟩ := hmem a
        obtain ⟨yb, hyb, heb⟩ := hmem b
        have hyab : Submodule.Quotient.mk (ya + yb) ∈ X := by
          rw [Submodule.Quotient.mk_add]; exact X.add_mem hya hyb
        rw [hf a ya hya hea, hf b yb hyb heb, hf (a + b) (ya + yb) hyab
          (by rw [map_add, hea, heb]; rfl), ← map_add]
        congr 1 }
  refine ⟨X', π', fun x' => Iff.rfl, ?_⟩
  intro y hy hy'
  exact hf ⟨ι y, hy'⟩ y hy rfl

end Transport

end R1RealPrimeAsm

section Main

open Polynomial CuspForm.TWLevel R1RealPrimeAsm

set_option hygiene false in
local notation "TT" => HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc

set_option hygiene false in
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

set_option hygiene false in
local notation "Tor" n => (Fin b → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
  (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n)))

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem R1RealPrimeAsm.main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (r : ℕ) [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqinj : Function.Injective qv)
    (hqv : ∀ i, (qv i).Prime ∧ qv i ∉ S) (hqr : ∀ i, qv i ≠ r)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (α : Fin t → ResidueField 𝒪)
    (hcQ : OpComm N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ))
    (hdc : DiaComm N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ))
    (hloc : IsLocalRing TT)
    (hlh : haveI := hloc; IsLocalHom (algebraMap 𝒪 TT))
    (ρ' : haveI := hloc; GaloisRepAdic TT)
    (htr : haveI := hloc
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ level N r qv),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            ρ'.trace σ = HeckeRing.T N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc ℓ hℓ hℓS hℓL)
    (hres : haveI := hloc; haveI := hlh
      ρ'.residual.IsEquiv (ρbar.baseChangeAlong
        (IsLocalRing.ResidueField.map (algebraMap 𝒪 TT))))
    (hpL : ¬ p ∣ level N r qv)
    (I : Ideal TT) (hI : Finite (TT ⧸ I)) :
    haveI := hloc
    ∃ (δ : Gal →* (ZMod (level N r qv))ˣ),
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, δ σ = 1) ∧
      GaloisFactorsThroughFiniteLevel δ ∧
      ∃ (n b : ℕ)
        (star : Gal →* AddAut (Tor n)),
        (∀ (σ : Gal) (x : Tor n) (i : Fin b),
          ((star σ x i : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
              (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))) :
              ModularCurve.JH (level N r qv) (HQ N r qv p πΔ)) =
            ModularCurve.diamondHBar (level N r qv) (HQ N r qv p πΔ) (δ σ)
              (σ • ((x i : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
                (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))) :
                ModularCurve.JH (level N r qv) (HQ N r qv p πΔ)))) ∧
        ∃ X : AddSubgroup (Tor n),
          (∀ (σ : Gal), ∀ x ∈ X, star σ x ∈ X) ∧
          ∃ π : ↥X →+ (ρ'.V ⧸ (I • (⊤ : Submodule TT ρ'.V))),
            Function.Surjective π ∧
            ∀ (σ : Gal) (x y : ↥X), (y : Tor n) = star σ x → π y = ρ'.levelAction I σ (π x) := by
  haveI := hloc
  haveI := hlh

  have hML : Nontrivial (ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ) := by
    by_contra hnt
    haveI : Subsingleton (ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ) :=
      not_nontrivial_iff_subsingleton.mp hnt
    have h01 : (0 : TT) = 1 :=
      HeckeRing.ext N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc (Subsingleton.elim _ _)
    exact zero_ne_one h01
  obtain ⟨hfinT, hnoeT, -⟩ :=
    CuspForm.TWLevel.HeckeRing.finite_and_isLocalRing_and_isAdicComplete p hp𝒪 (↑S : Set ℕ) N r θ t
      qv πΔ α hcQ hdc hML
  haveI := hfinT
  haveI := hnoeT
  haveI hred : IsReduced TT :=
    CuspForm.TWLevel.HeckeRing.isReduced N r qv (↑S : Set ℕ) (HQ N r qv p πΔ) θ α hcQ hdc
  have hpT : (p : TT) ∈ maximalIdeal TT := by
    have h := map_nonunit (algebraMap 𝒪 TT) _ hp𝒪
    simpa only [map_natCast] using h

  have habsT : ρ'.residual.IsAbsolutelyIrreducible := by
    obtain ⟨e⟩ := hres
    exact residual_isAbsolutelyIrreducible_of_equiv e (habs.baseChangeAlong _)
  have hspan : Submodule.span TT (Set.range ⇑ρ'.ρ) = ⊤ :=
    GaloisRepAdic.span_range_eq_top_of_residual_isAbsolutelyIrreducible ρ' habsT

  have hC1 :=
    CuspForm.TWLevel.HeckeRing.exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level
      p hp𝒪 ρbar habs S N hNS r hr hrN θ hθ t qv hqinj hqv hqr πΔ α hcQ hdc hpL
  obtain ⟨b, δ, hδ, hδc, hC1'⟩ := hC1
  obtain ⟨Y, iY1, iY2, iY3, iY4, iY5, iY6, hC1''⟩ := hC1'
  obtain ⟨ρY, D, hfaith, hDcomm, hC1'''⟩ := hC1''
  obtain ⟨hcont, hES, htors⟩ := hC1'''

  have hES' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (hℓL : ¬ ℓ ∣ level N r qv), ℓ ≠ p →
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : Gal, P.IsFrobeniusAt σ ℓ →
          ρY σ * ρY σ - (ρ'.trace σ) • ρY σ
            + (ℓ : TT) • D (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)) = 0 := by
    intro ℓ hℓ hℓS hℓL hℓp P hP σ hσ
    have hℓS' : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS (Finset.mem_coe.mp h)
    rw [htr ℓ hℓ hℓS' hℓL P hP σ hσ]
    exact hES ℓ hℓ hℓS' hℓL hℓp P hP σ hσ
  have h4 := @GaloisRepAdic.exists_quadraticRelation_forall_of_frobenius 𝒪 _ _ _ _ _ p _ hp𝒪 TT _ hloc _
    hfinT hlh ρ' Y iY1 iY2 iY3 iY4 iY5 ρY hcont (level N r qv) _ D hDcomm S hES'
  obtain ⟨cχ, χ, hrel⟩ := h4

  have h5 := @Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced
    𝒪 _ _ _ TT _ _ hfinT hred Gal _ ρ'.V _ _ _ _ ρ'.finrank_eq ρ'.ρ hspan Y iY1 iY2 iY3 iY4 iY5 iY6
    hfaith ρY ((ZMod (level N r qv))ˣ) _ _ D hDcomm χ cχ hrel
  obtain ⟨j, hjinj, hjG⟩ := h5

  have h6 := @exists_pow_mem_of_finite_quotient TT _ hloc (p : TT) hpT I hI
  obtain ⟨c, hpc⟩ := h6

  have iY7 : Module.Finite TT Y := @Module.Finite.of_restrictScalars_finite 𝒪 TT Y _ _ _ iY3 iY2 _ iY4 iY5
  have h7 := @exists_stable_submodule_surjective_equivariant TT _ Gal _ hnoeT ρ'.V Y _ _ iY1 iY2 iY7
    ρ'.ρ ρY j hjinj hjG (p : TT) c
  obtain ⟨m, Xq, hXq, πq, hπqsurj, hπqeq⟩ := h7

  have h8 := htors m
  obtain ⟨star, h8'⟩ := h8
  obtain ⟨hstar, h8''⟩ := h8'
  obtain ⟨ι, hιker, hιeq⟩ := h8''

  have hle : (Ideal.span {(p : TT)} ^ c • ⊤ : Submodule TT ρ'.V) ≤
      (I • (⊤ : Submodule TT ρ'.V)).comap (LinearMap.id : ρ'.V →ₗ[TT] ρ'.V) := by
    rw [Submodule.comap_id]
    have hI' : Ideal.span {(p : TT)} ^ c ≤ I := by
      rw [Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
      exact hpc
    exact Submodule.smul_mono hI' le_rfl
  let fq : (ρ'.V ⧸ (Ideal.span {(p : TT)} ^ c • ⊤ : Submodule TT ρ'.V)) →ₗ[TT]
      (ρ'.V ⧸ (I • (⊤ : Submodule TT ρ'.V))) :=
    Submodule.mapQ _ _ LinearMap.id hle
  have h9 := @exists_transport TT _ Y iY1 iY2 _ _ _ _ (Ideal.span {(p : TT)} ^ m • ⊤ : Submodule TT Y) ι hιker
    Xq ((fq.toAddMonoidHom).comp πq.toAddMonoidHom)
  obtain ⟨X', π', h9'⟩ := h9
  obtain ⟨hX'mem, hπ'⟩ := h9'
  refine ⟨δ, hδ, hδc, m, b, star, hstar, X', ?_, π', ?_, ?_⟩

  ·
    intro σ x' hx'
    obtain ⟨y, hy, rfl⟩ := (hX'mem x').mp hx'
    rw [← hιeq]
    exact (hX'mem _).mpr ⟨ρY σ y, hXq σ y hy, rfl⟩
  ·
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H v =>
      obtain ⟨⟨xq, hxq⟩, hx⟩ := hπqsurj (Submodule.Quotient.mk v)
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ xq
      have hyX : Submodule.Quotient.mk y ∈ Xq := by rw [hy]; exact hxq
      refine ⟨⟨ι y, (hX'mem _).mpr ⟨y, hyX, rfl⟩⟩, ?_⟩
      rw [hπ' y hyX]
      show fq (πq ⟨Submodule.Quotient.mk y, hyX⟩) = Submodule.Quotient.mk v
      have : (⟨Submodule.Quotient.mk y, hyX⟩ : ↥Xq) = ⟨xq, hxq⟩ := Subtype.ext hy
      rw [this, hx]
      rfl
  ·
    rintro σ ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hx' := (hX'mem x).mp hx
    obtain ⟨yx, hyx, hex⟩ := hx'
    change y = star σ x at hxy
    have hy' : y = ι (ρY σ yx) := by rw [hxy, ← hex, hιeq]
    have hyX : Submodule.Quotient.mk (ρY σ yx) ∈ Xq := hXq σ yx hyx
    subst hy'
    subst hex
    have E1 : π' ⟨ι (ρY σ yx), hy⟩ = fq (πq ⟨Submodule.Quotient.mk (ρY σ yx), hyX⟩) :=
      hπ' (ρY σ yx) hyX hy
    have E2 : π' ⟨ι yx, hx⟩ = fq (πq ⟨Submodule.Quotient.mk yx, hyx⟩) := hπ' yx hyx hx
    refine E1.trans (Eq.trans ?_ (congrArg (ρ'.levelAction I σ) E2).symm)
    refine (congrArg fq (hπqeq σ yx hyx)).trans ?_
    generalize πq ⟨Submodule.Quotient.mk yx, hyx⟩ = q
    induction q using Submodule.Quotient.induction_on with
    | H v => rfl

end Main

open Polynomial IsLocalRing CuspForm.TWLevel in
set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)

    (r : ℕ) [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)

    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))

    (t : ℕ) (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqinj : Function.Injective qv)
    (hqv : ∀ i, (qv i).Prime ∧ qv i ∉ S) (hqr : ∀ i, qv i ≠ r)
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (α : Fin t → ResidueField 𝒪)

    (hcQ : OpComm N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ))
    (hdc : DiaComm N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ))

    (hloc : IsLocalRing (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc))
    (hlh : haveI := hloc
      IsLocalHom (algebraMap 𝒪 (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)))

    (ρ' : haveI := hloc; GaloisRepAdic (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc))
    (htr : haveI := hloc
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ level N r qv),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            ρ'.trace σ = HeckeRing.T N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc ℓ hℓ hℓS hℓL)
    (hres : haveI := hloc; haveI := hlh
      ρ'.residual.IsEquiv (ρbar.baseChangeAlong
        (IsLocalRing.ResidueField.map (algebraMap 𝒪 (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)))))

    (hpL : ¬ p ∣ level N r qv)

    (I : Ideal (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc))
    (hI : Finite (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc ⧸ I)) :
    haveI := hloc
    ∃ (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod (level N r qv))ˣ),

      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, δ σ = 1) ∧

      GaloisFactorsThroughFiniteLevel δ ∧
      ∃ (n b : ℕ)

        (star : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
          AddAut (Fin b → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
            (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n)))),
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (x : Fin b → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
            (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))) (i : Fin b),
          ((star σ x i : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
              (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))) :
              ModularCurve.JH (level N r qv) (HQ N r qv p πΔ)) =
            ModularCurve.diamondHBar (level N r qv) (HQ N r qv p πΔ) (δ σ)
              (σ • ((x i : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
                (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))) :
                ModularCurve.JH (level N r qv) (HQ N r qv p πΔ)))) ∧

        ∃ X : AddSubgroup (Fin b → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
            (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))),
          (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ X, star σ x ∈ X) ∧
          ∃ π : ↥X →+ (ρ'.V ⧸ (I • (⊤ : Submodule
              (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) ρ'.V))),
            Function.Surjective π ∧
            ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : ↥X),
              (y : Fin b → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
                (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))) = star σ x →
              π y = ρ'.levelAction I σ (π x) :=
  R1RealPrimeAsm.main p hp𝒪 ρbar habs S N hNS r hr hrN θ hθ t qv hqinj hqv hqr πΔ α hcQ hdc hloc hlh ρ' htr
    hres hpL I hI

end S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_surjective_pi_torsion_jH_levelQuotient_of_not_dvd_level
end P2MW
export P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_surjective_pi_torsion_jH_levelQuotient_of_not_dvd_level (solution)

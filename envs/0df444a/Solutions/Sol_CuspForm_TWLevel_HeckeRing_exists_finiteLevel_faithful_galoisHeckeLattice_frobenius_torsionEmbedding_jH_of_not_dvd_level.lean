-- Prove2me | solution 1 for CuspForm.TWLevel.HeckeRing.exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2cf8faba-7e90-5c06-96fd-75d28d955839

import Mathlib
import Definitions.Def_CuspForm_TWLevelHeckeRing
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_CuspForm_TWLevel_exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH
import Theorems.Thm_ModularCurve_exists_character_frobeniusQuadratic_diamondTwist_tateModule_jH
import Theorems.Thm_TateModule_exists_baseChange_pi_torsionBy_ker_eq_pow_smul
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm
import Theorems.Thm_ModularCurve_JH_exists_finiteDimensional_smul_eq_self_of_torsion
import Theorems.Thm_CohCarrier_HeckeData_finite_ML_and_free_ML
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_RibetIrr_module_finite_padicInt_of_isDiscreteValuationRing
import Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level
p2m_attr_erase "instance" "IharaLemma.IdempotentSplitting.isScalarTower_base_cornerModule IharaLemma.IdempotentSplitting.isScalarTower_base_cornerRing IharaLemma.IdempotentSplitting.algebraBaseCornerRing IharaLemma.IdempotentSplitting.smulCornerModule IharaLemma.IdempotentSplitting.moduleCornerModule IharaLemma.IdempotentSplitting.isLocalRing_cornerRing IharaLemma.IdempotentSplitting.coeOutCornerRing IharaLemma.IdempotentSplitting.isMaximal_𝔪 IharaLemma.IdempotentSplitting.isScalarTower_cornerModule IharaLemma.IdempotentSplitting.isLocalization_cornerRing CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par CohCarrier.GammaHLower_finiteIndex AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
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
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

namespace A2Lattice

section Dual

variable {𝒪 : Type} [CommRing 𝒪] {M : Type} [AddCommGroup M] [Module 𝒪 M]
  {T : Type} [CommRing T] [Algebra 𝒪 T]

@[nolint unusedArguments]
def DualLattice (_act : T →ₐ[𝒪] Module.End 𝒪 M) : Type := Module.Dual 𝒪 M

variable (act : T →ₐ[𝒪] Module.End 𝒪 M)

scoped instance DualLattice.instAddCommGroup : AddCommGroup (DualLattice act) :=
  inferInstanceAs (AddCommGroup (Module.Dual 𝒪 M))

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice"
scoped instance DualLattice.instModule : Module 𝒪 (DualLattice act) :=
  inferInstanceAs (Module 𝒪 (Module.Dual 𝒪 M))

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice"
namespace DualLattice

def toDual : DualLattice act ≃ₗ[𝒪] Module.Dual 𝒪 M := LinearEquiv.refl 𝒪 _

def ofDual : Module.Dual 𝒪 M ≃ₗ[𝒪] DualLattice act := LinearEquiv.refl 𝒪 _

@[scoped simp] theorem toDual_ofDual (y : Module.Dual 𝒪 M) : toDual act (ofDual act y) = y := rfl
@[scoped simp] theorem ofDual_toDual (y : DualLattice act) : ofDual act (toDual act y) = y := rfl

scoped instance instSMulT : SMul T (DualLattice act) :=
  ⟨fun x y => ofDual act ((toDual act y) ∘ₗ act x)⟩

theorem smul_def (x : T) (y : DualLattice act) :
    x • y = ofDual act ((toDual act y) ∘ₗ act x) := rfl

@[scoped simp] theorem toDual_smul (x : T) (y : DualLattice act) :
    toDual act (x • y) = (toDual act y) ∘ₗ act x := rfl

theorem toDual_smul_apply (x : T) (y : DualLattice act) (m : M) :
    toDual act (x • y) m = toDual act y (act x m) := rfl

@[scoped simp] theorem toDual_osmul (c : 𝒪) (y : DualLattice act) :
    toDual act (c • y) = c • toDual act y := rfl

theorem toDual_injective : Function.Injective (toDual act) := fun _ _ h => h

scoped instance instModuleT : Module T (DualLattice act) where
  one_smul y := by
    apply toDual_injective act
    rw [toDual_smul, map_one]
    rfl
  mul_smul x x' y := by
    apply toDual_injective act
    rw [toDual_smul, toDual_smul, toDual_smul, map_mul, LinearMap.comp_assoc]
    congr 1
    show act x * act x' = act x' * act x
    rw [← map_mul, ← map_mul, mul_comm]
  smul_zero x := by
    apply toDual_injective act
    rw [toDual_smul]
    rfl
  smul_add x y y' := by
    apply toDual_injective act
    rw [toDual_smul]
    rfl
  add_smul x x' y := by
    apply toDual_injective act
    rw [toDual_smul, map_add]
    show toDual act y ∘ₗ (act x + act x') = toDual act y ∘ₗ act x + toDual act y ∘ₗ act x'
    rw [LinearMap.comp_add]
  zero_smul y := by
    apply toDual_injective act
    rw [toDual_smul, map_zero, LinearMap.comp_zero]
    rfl

scoped instance instIsScalarTower : IsScalarTower 𝒪 T (DualLattice act) :=
  ⟨fun c x y => by
    apply toDual_injective act
    rw [toDual_smul, toDual_osmul, toDual_smul, map_smul, LinearMap.comp_smul]⟩

def smulEnd (x : T) : Module.End 𝒪 (DualLattice act) where
  toFun y := x • y
  map_add' y y' := smul_add x y y'
  map_smul' c y := by
    apply toDual_injective act
    rw [toDual_smul, toDual_osmul, RingHom.id_apply, toDual_osmul, toDual_smul, LinearMap.smul_comp]

@[scoped simp] theorem smulEnd_apply (x : T) (y : DualLattice act) : smulEnd act x y = x • y := rfl

theorem algebraMap_smul' (c : 𝒪) (y : DualLattice act) : (algebraMap 𝒪 T c) • y = c • y := by
  rw [Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

theorem natCast_smul' (n : ℕ) (y : DualLattice act) : (n : T) • y = (n : 𝒪) • y := by
  rw [← map_natCast (algebraMap 𝒪 T), algebraMap_smul']

scoped instance instIsTorsionFree [IsDomain 𝒪] : Module.IsTorsionFree 𝒪 (DualLattice act) := by
  refine ⟨fun r hr => ?_⟩
  intro y y' h
  have h0 : r • y = r • y' := h
  apply toDual_injective act
  apply LinearMap.ext
  intro m
  have h' : toDual act (r • y) m = toDual act (r • y') m := by rw [h0]
  rw [toDual_osmul, toDual_osmul, LinearMap.smul_apply, LinearMap.smul_apply] at h'
  exact hr.left h'

scoped instance instFinite [Module.Finite 𝒪 M] [Module.Free 𝒪 M] : Module.Finite 𝒪 (DualLattice act) :=
  inferInstanceAs (Module.Finite 𝒪 (Module.Dual 𝒪 M))

theorem eq_zero_of_forall_smul_eq_zero [Module.Free 𝒪 M] (hinj : Function.Injective act) (x : T)
    (h : ∀ y : DualLattice act, x • y = 0) : x = 0 := by
  apply hinj
  rw [map_zero]
  apply LinearMap.ext
  intro m
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff 𝒪 (act x m)).mp fun φ => ?_
  have := congrArg (fun y => toDual act y m) (h (ofDual act φ))
  simp only [toDual_smul_apply, toDual_ofDual] at this
  exact this

theorem mem_span_pow_smul_top_iff (p : ℕ) (n : ℕ) (y : DualLattice act) :
    y ∈ (Ideal.span {(p : T)}) ^ n • (⊤ : Submodule T (DualLattice act)) ↔
      ∃ y' : DualLattice act, y = ((p : 𝒪) ^ n) • y' := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  constructor
  · intro h
    obtain ⟨y', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
    refine ⟨y', ?_⟩
    rw [← Nat.cast_pow, ← Nat.cast_pow, natCast_smul']
  · rintro ⟨y', rfl⟩
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y', Submodule.mem_top, ?_⟩
    rw [← Nat.cast_pow, ← Nat.cast_pow, natCast_smul']

end DualLattice
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice"

end Dual
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice"

section Transport

variable {𝒪 : Type} [CommRing 𝒪] {Y W : Type} [AddCommGroup Y] [Module 𝒪 Y]
  [AddCommGroup W] [Module 𝒪 W]

structure IsSummandEmbedding (Θ : Y →ₗ[𝒪] W) (E : W →ₗ[𝒪] W) : Prop where
  injective : Function.Injective Θ
  idem : E ∘ₗ E = E
  range_eq : LinearMap.range Θ = LinearMap.range E

def commSubmonoid (E : W →ₗ[𝒪] W) : Submonoid (Module.End 𝒪 W) where
  carrier := {P | E ∘ₗ P = P ∘ₗ E}
  one_mem' := by
    show E ∘ₗ (1 : Module.End 𝒪 W) = 1 ∘ₗ E
    rw [Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  mul_mem' := by
    intro P Q hP hQ
    show E ∘ₗ (P ∘ₗ Q) = (P ∘ₗ Q) ∘ₗ E
    rw [← LinearMap.comp_assoc, hP, LinearMap.comp_assoc, hQ, LinearMap.comp_assoc]

theorem comp_mul_of_comp_eq {E P Q : Module.End 𝒪 W} (hP : E ∘ₗ P = P ∘ₗ E) (hQ : E ∘ₗ Q = Q ∘ₗ E) :
    E ∘ₗ (P * Q) = (P * Q) ∘ₗ E :=
  (commSubmonoid E).mul_mem hP hQ

namespace IsSummandEmbedding

variable {Θ : Y →ₗ[𝒪] W} {E : W →ₗ[𝒪] W} (h : IsSummandEmbedding Θ E)
include h

theorem apply_E_Θ (y : Y) : E (Θ y) = Θ y := by
  have hy : Θ y ∈ LinearMap.range E := h.range_eq ▸ LinearMap.mem_range_self Θ y
  obtain ⟨w, hw⟩ := hy
  rw [← hw, ← LinearMap.comp_apply, h.idem]

theorem E_apply_mem_range (w : W) : E w ∈ LinearMap.range Θ :=
  h.range_eq ▸ LinearMap.mem_range_self E w

noncomputable def equivRange : Y ≃ₗ[𝒪] ↥(LinearMap.range Θ) :=
  LinearEquiv.ofInjective Θ h.injective

@[scoped simp] theorem equivRange_apply (y : Y) : (h.equivRange y : W) = Θ y := rfl

theorem Θ_equivRange_symm (w : ↥(LinearMap.range Θ)) : Θ (h.equivRange.symm w) = w := by
  have := LinearEquiv.apply_symm_apply h.equivRange w
  exact congrArg Subtype.val this

noncomputable def tr : Module.End 𝒪 W →ₗ[𝒪] Module.End 𝒪 Y where
  toFun P := h.equivRange.symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range Θ) (E ∘ₗ P ∘ₗ Θ) (fun y => h.E_apply_mem_range (P (Θ y)))
  map_add' P Q := by
    apply LinearMap.ext; intro y
    apply h.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, map_add,
      Θ_equivRange_symm, LinearMap.codRestrict_apply]
  map_smul' c P := by
    apply LinearMap.ext; intro y
    apply h.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply, map_smul,
      Θ_equivRange_symm, LinearMap.codRestrict_apply, RingHom.id_apply]

theorem Θ_tr (P : Module.End 𝒪 W) (y : Y) : Θ (h.tr P y) = E (P (Θ y)) := by
  show Θ (h.equivRange.symm _) = _
  rw [Θ_equivRange_symm]
  rfl

theorem Θ_tr_of_comm {P : Module.End 𝒪 W} (hP : E ∘ₗ P = P ∘ₗ E) (y : Y) :
    Θ (h.tr P y) = P (Θ y) := by
  rw [Θ_tr, ← LinearMap.comp_apply, hP, LinearMap.comp_apply, h.apply_E_Θ]

theorem tr_one : h.tr 1 = 1 := by
  apply LinearMap.ext; intro y; apply h.injective
  rw [Θ_tr, Module.End.one_apply, Module.End.one_apply, h.apply_E_Θ]

theorem tr_mul {P Q : Module.End 𝒪 W} (hQ : E ∘ₗ Q = Q ∘ₗ E) : h.tr (P * Q) = h.tr P * h.tr Q := by
  apply LinearMap.ext; intro y; apply h.injective
  rw [Θ_tr, Module.End.mul_apply, Module.End.mul_apply, Θ_tr, h.Θ_tr_of_comm hQ]

noncomputable def trHom : ↥(commSubmonoid E) →* Module.End 𝒪 Y where
  toFun P := h.tr (P : Module.End 𝒪 W)
  map_one' := h.tr_one
  map_mul' P Q := h.tr_mul Q.2

@[scoped simp] theorem trHom_apply (P : ↥(commSubmonoid E)) : h.trHom P = h.tr (P : Module.End 𝒪 W) := rfl

theorem tr_comm_apply {P Q : Module.End 𝒪 W} (hP : E ∘ₗ P = P ∘ₗ E) (hQ : E ∘ₗ Q = Q ∘ₗ E)
    (hPQ : P * Q = Q * P) (y : Y) : h.tr P (h.tr Q y) = h.tr Q (h.tr P y) := by
  rw [← Module.End.mul_apply, ← h.tr_mul hQ, hPQ, h.tr_mul hP, Module.End.mul_apply]

theorem tr_quadratic_apply {P B D : Module.End 𝒪 W} (hP : E ∘ₗ P = P ∘ₗ E) (ℓ : ℕ)
    (hrel : P * P - B * P + ℓ • D = 0) (y : Y) :
    h.tr P (h.tr P y) - h.tr B (h.tr P y) + ℓ • h.tr D y = 0 := by
  have := congrArg h.tr hrel
  rw [map_add, map_sub, h.tr_mul hP, h.tr_mul hP, map_nsmul, map_zero] at this
  have := congrArg (fun f : Module.End 𝒪 Y => f y) this
  simpa only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.zero_apply] using this

theorem tr_eq_of_intertwine {A : Module.End 𝒪 Y} {B : Module.End 𝒪 W}
    (hAB : ∀ y, Θ (A y) = B (Θ y)) (hB : E ∘ₗ B = B ∘ₗ E) : h.tr B = A := by
  apply LinearMap.ext; intro y; apply h.injective
  rw [h.Θ_tr_of_comm hB, hAB]

theorem tr_comm_of_intertwine {A : Module.End 𝒪 Y} {B P : Module.End 𝒪 W}
    (hAB : ∀ y, Θ (A y) = B (Θ y)) (hP : E ∘ₗ P = P ∘ₗ E) (hPB : P ∘ₗ B = B ∘ₗ P) (y : Y) :
    h.tr P (A y) = A (h.tr P y) := by
  apply h.injective
  rw [h.Θ_tr_of_comm hP, hAB, hAB, h.Θ_tr_of_comm hP, ← LinearMap.comp_apply, hPB,
    LinearMap.comp_apply]

theorem exists_eq_smul_iff (c : 𝒪) (y : Y) :
    (∃ y' : Y, y = c • y') ↔ ∃ w : W, Θ y = c • w := by
  constructor
  · rintro ⟨y', rfl⟩
    exact ⟨Θ y', map_smul Θ c y'⟩
  · rintro ⟨w, hw⟩
    have hEw : Θ y = c • E w := by rw [← h.apply_E_Θ y, hw, map_smul]
    obtain ⟨y', hy'⟩ : E w ∈ LinearMap.range Θ := h.E_apply_mem_range w
    refine ⟨y', h.injective ?_⟩
    rw [hEw, map_smul, hy']

theorem exists_tr_sub_eq_smul {P : Module.End 𝒪 W} (hP : E ∘ₗ P = P ∘ₗ E) (c : 𝒪)
    (hdiv : ∀ z : W, ∃ w : W, P z - z = c • w) (y : Y) :
    ∃ y' : Y, h.tr P y - y = c • y' := by
  rw [h.exists_eq_smul_iff]
  obtain ⟨w, hw⟩ := hdiv (Θ y)
  exact ⟨w, by rw [map_sub, h.Θ_tr_of_comm hP, hw]⟩

end IsSummandEmbedding
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding"

end Transport
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding"

section Generated

variable {𝒪 : Type} [CommRing 𝒪] {T : Type} [CommRing T] [Algebra 𝒪 T]
  {Y : Type} [AddCommGroup Y] [Module 𝒪 Y] [Module T Y] [IsScalarTower 𝒪 T Y]

theorem smul_comm_of_generators (G : Set T)
    (hgen : ∀ P : T → Prop, (∀ g ∈ G, P g) → (∀ c : 𝒪, P (algebraMap 𝒪 T c)) →
      (∀ x y, P x → P y → P (x + y)) → (∀ x y, P x → P y → P (x * y)) → ∀ x, P x)
    (f : Y →ₗ[𝒪] Y) (hf : ∀ g ∈ G, ∀ y : Y, f (g • y) = g • f y) (x : T) (y : Y) :
    f (x • y) = x • f y := by
  revert y
  refine hgen (fun x => ∀ y, f (x • y) = x • f y) hf ?_ ?_ ?_ x
  · intro c y
    rw [algebraMap_smul, algebraMap_smul, map_smul]
  · intro x x' hx hx' y
    rw [add_smul, add_smul, map_add, hx, hx']
  · intro x x' hx hx' y
    rw [mul_smul, mul_smul, hx, hx']

def toEndOfGenerators (G : Set T)
    (hgen : ∀ P : T → Prop, (∀ g ∈ G, P g) → (∀ c : 𝒪, P (algebraMap 𝒪 T c)) →
      (∀ x y, P x → P y → P (x + y)) → (∀ x y, P x → P y → P (x * y)) → ∀ x, P x)
    (f : Y →ₗ[𝒪] Y) (hf : ∀ g ∈ G, ∀ y : Y, f (g • y) = g • f y) : Module.End T Y where
  toFun := f
  map_add' := map_add f
  map_smul' x y := smul_comm_of_generators G hgen f hf x y

@[scoped simp] theorem toEndOfGenerators_apply (G : Set T) (hgen) (f : Y →ₗ[𝒪] Y) (hf) (y : Y) :
    toEndOfGenerators G hgen f hf y = f y := rfl

def liftHomOfGenerators {G₀ : Type} [Monoid G₀] (G : Set T)
    (hgen : ∀ P : T → Prop, (∀ g ∈ G, P g) → (∀ c : 𝒪, P (algebraMap 𝒪 T c)) →
      (∀ x y, P x → P y → P (x + y)) → (∀ x y, P x → P y → P (x * y)) → ∀ x, P x)
    (f : G₀ →* Module.End 𝒪 Y) (hf : ∀ (a : G₀), ∀ g ∈ G, ∀ y : Y, f a (g • y) = g • f a y) :
    G₀ →* Module.End T Y where
  toFun a := toEndOfGenerators G hgen (f a) (hf a)
  map_one' := by
    apply LinearMap.ext; intro y
    rw [toEndOfGenerators_apply, map_one, Module.End.one_apply, Module.End.one_apply]
  map_mul' a a' := by
    apply LinearMap.ext; intro y
    rw [toEndOfGenerators_apply, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      toEndOfGenerators_apply, toEndOfGenerators_apply]

end Generated
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding"

end A2Lattice
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice"

open TensorProduct

namespace A2Lattice

section Tate

variable (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem diamondHBar_one (x : ModularCurve.JH L H) : ModularCurve.diamondHBar L H 1 x = x := by
  have h := ModularCurve.diamondHBar_mul L H 1 1 x
  rw [mul_one] at h

  have hinj : Function.Injective (ModularCurve.diamondHBar L H 1) := by
    intro a b hab
    rw [ModularCurve.diamondHBar_apply, ModularCurve.diamondHBar_apply] at hab
    exact smul_left_cancel _ hab
  exact (hinj h).symm

theorem galois_smul_diamondHBar (σ : Gal) (d : (ZMod L)ˣ) (x : ModularCurve.JH L H) :
    σ • ModularCurve.diamondHBar L H d x = ModularCurve.diamondHBar L H d (σ • x) := by
  have := ModularCurve.galois_smul_genOpH_comm L H (∅ : Set ℕ) σ (CohCarrier.Gen.dia d) x
  rwa [ModularCurve.genOpH_dia] at this

theorem tateGenOpH_dia_mul (d d' : (ZMod L)ˣ) :
    ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.dia (d * d')) =
      ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.dia d) *
        ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.dia d') := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  rw [Module.End.mul_apply, ModularCurve.tateGenOpH_apply_coe, ModularCurve.tateGenOpH_apply_coe,
    ModularCurve.tateGenOpH_apply_coe, ModularCurve.genOpH_dia, ModularCurve.genOpH_dia,
    ModularCurve.genOpH_dia, ModularCurve.diamondHBar_mul]

theorem tateGenOpH_dia_one :
    ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.dia 1) = 1 := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  rw [ModularCurve.tateGenOpH_apply_coe, ModularCurve.genOpH_dia, diamondHBar_one]
  rfl

@[irreducible] noncomputable def tateDia :
    (ZMod L)ˣ →* Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)) where
  toFun d := ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.dia d)
  map_one' := tateGenOpH_dia_one L H S p
  map_mul' d d' := tateGenOpH_dia_mul L H S p d d'

theorem tateDia_def (d : (ZMod L)ˣ) :
    tateDia L H S p d = ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.dia d) := by
  rw [tateDia]; rfl

@[irreducible] noncomputable def tateT (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) :
    Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)) :=
  ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓL)

theorem tateT_def (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) :
    tateT L H S p ℓ hℓ hℓS hℓL = ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓL) := by
  rw [tateT]

@[irreducible] noncomputable def tateGal :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)) :=
  ModularCurve.JH.tateGaloisRep L H p

theorem tateGal_def (σ : Gal) : tateGal L H p σ = ModularCurve.JH.tateGaloisRep L H p σ := by
  rw [tateGal]

theorem rep_gal_eq (σ : Gal) : TateModule.rep p (ModularCurve.JH L H) Gal σ = tateGal L H p σ := by
  rw [tateGal_def]

theorem rep_dia_eq (d : (ZMod L)ˣ) :
    TateModule.rep p (ModularCurve.JH L H) (AddMonoid.End (ModularCurve.JH L H))
      (ModularCurve.genOpH L H S (CohCarrier.Gen.dia d)) = tateDia L H S p d := by
  rw [tateDia_def]; rfl

theorem tateGaloisRep_mul_tateGenOpH (σ : Gal) (g : CohCarrier.Gen L S) :
    ModularCurve.JH.tateGaloisRep L H p σ * ModularCurve.tateGenOpH L H S p g =
      ModularCurve.tateGenOpH L H S p g * ModularCurve.JH.tateGaloisRep L H p σ := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  rw [Module.End.mul_apply, Module.End.mul_apply, ModularCurve.JH.tateGaloisRep_apply_coe,
    ModularCurve.tateGenOpH_apply_coe, ModularCurve.tateGenOpH_apply_coe,
    ModularCurve.JH.tateGaloisRep_apply_coe]
  exact ModularCurve.galois_smul_genOpH_comm L H S σ g _

theorem tateGenOpH_T_mul_dia (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (d : (ZMod L)ˣ) :
    ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓL) *
        ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.dia d) =
      ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.dia d) *
        ModularCurve.tateGenOpH L H S p (CohCarrier.Gen.T ℓ hℓ hℓS hℓL) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  rw [Module.End.mul_apply, Module.End.mul_apply, ModularCurve.tateGenOpH_apply_coe,
    ModularCurve.tateGenOpH_apply_coe, ModularCurve.tateGenOpH_apply_coe,
    ModularCurve.tateGenOpH_apply_coe, ModularCurve.genOpH_dia, ModularCurve.genOpH_T]
  exact ModularCurve.heckeOperatorHAlong_diamondHBar_comm L H ℓ d _

theorem tateGal_mul_tateT (σ : Gal) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) :
    tateGal L H p σ * tateT L H S p ℓ hℓ hℓS hℓL = tateT L H S p ℓ hℓ hℓS hℓL * tateGal L H p σ := by
  rw [tateGal_def, tateT_def]
  exact tateGaloisRep_mul_tateGenOpH L H S p σ _

theorem tateGal_mul_tateDia (σ : Gal) (d : (ZMod L)ˣ) :
    tateGal L H p σ * tateDia L H S p d = tateDia L H S p d * tateGal L H p σ := by
  rw [tateGal_def, tateDia_def]
  exact tateGaloisRep_mul_tateGenOpH L H S p σ _

theorem tateT_mul_tateDia (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (d : (ZMod L)ˣ) :
    tateT L H S p ℓ hℓ hℓS hℓL * tateDia L H S p d = tateDia L H S p d * tateT L H S p ℓ hℓ hℓS hℓL := by
  rw [tateT_def, tateDia_def]
  exact tateGenOpH_T_mul_dia L H S p ℓ hℓ hℓS hℓL d

theorem tateDia_comm (d d' : (ZMod L)ˣ) :
    tateDia L H S p d * tateDia L H S p d' = tateDia L H S p d' * tateDia L H S p d := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem twist_mul_tateT (ρ' : Gal →* Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)))
    (δ : Gal →* (ZMod L)ˣ) (hρ' : ∀ σ, ρ' σ = tateDia L H S p (δ σ) * tateGal L H p σ)
    (σ : Gal) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) :
    ρ' σ * tateT L H S p ℓ hℓ hℓS hℓL = tateT L H S p ℓ hℓ hℓS hℓL * ρ' σ := by
  have hGT := fun x => congrArg (fun f : Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)) => f x)
    (tateGal_mul_tateT L H S p σ ℓ hℓ hℓS hℓL)
  have hTD := fun x => congrArg (fun f : Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)) => f x)
    (tateT_mul_tateDia L H S p ℓ hℓ hℓS hℓL (δ σ))
  simp only [Module.End.mul_apply] at hGT hTD
  apply LinearMap.ext; intro x
  show ρ' σ (tateT L H S p ℓ hℓ hℓS hℓL x) = tateT L H S p ℓ hℓ hℓS hℓL (ρ' σ x)
  rw [hρ']
  show tateDia L H S p (δ σ) (tateGal L H p σ (tateT L H S p ℓ hℓ hℓS hℓL x)) =
    tateT L H S p ℓ hℓ hℓS hℓL (tateDia L H S p (δ σ) (tateGal L H p σ x))
  exact (congrArg (tateDia L H S p (δ σ)) (hGT x)).trans (hTD (tateGal L H p σ x)).symm

theorem twist_mul_tateDia (ρ' : Gal →* Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)))
    (δ : Gal →* (ZMod L)ˣ) (hρ' : ∀ σ, ρ' σ = tateDia L H S p (δ σ) * tateGal L H p σ)
    (σ : Gal) (u : (ZMod L)ˣ) :
    ρ' σ * tateDia L H S p u = tateDia L H S p u * ρ' σ := by
  have hGD := fun x => congrArg (fun f : Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)) => f x)
    (tateGal_mul_tateDia L H S p σ u)
  have hDD := fun x => congrArg (fun f : Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)) => f x)
    (tateDia_comm L H S p (δ σ) u)
  simp only [Module.End.mul_apply] at hGD hDD
  apply LinearMap.ext; intro x
  show ρ' σ (tateDia L H S p u x) = tateDia L H S p u (ρ' σ x)
  rw [hρ']
  show tateDia L H S p (δ σ) (tateGal L H p σ (tateDia L H S p u x)) =
    tateDia L H S p u (tateDia L H S p (δ σ) (tateGal L H p σ x))
  exact (congrArg (tateDia L H S p (δ σ)) (hGD x)).trans (hDD (tateGal L H p σ x))

theorem twist_eq_of_eq_one (ρ' : Gal →* Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H)))
    (δ : Gal →* (ZMod L)ˣ) (hρ' : ∀ σ, ρ' σ = tateDia L H S p (δ σ) * tateGal L H p σ)
    (σ : Gal) (hσ : δ σ = 1) : ρ' σ = tateGal L H p σ := by
  rw [hρ', hσ, map_one]
  apply LinearMap.ext; intro x
  show (1 : Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H))) (tateGal L H p σ x) = tateGal L H p σ x
  rfl

theorem baseChange_quadratic {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (P B D : Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H))) (ℓ : ℕ)
    (hrel : ∀ x, P (P x) - B (P x) + ℓ • D x = 0) :
    P.baseChange A * P.baseChange A - B.baseChange A * P.baseChange A + ℓ • D.baseChange A = 0 := by
  have hTa : P * P - B * P + ℓ • D = 0 := by
    apply LinearMap.ext; intro x
    exact hrel x
  have h1 : (P * P - B * P + ℓ • D).baseChange A =
      (0 : Module.End ℤ_[p] ↥(TateModule p (ModularCurve.JH L H))).baseChange A :=
    congrArg (LinearMap.baseChange A) hTa
  have e1 := LinearMap.baseChange_add (A := A) (P * P - B * P) (ℓ • D)
  have e2 := LinearMap.baseChange_sub (A := A) (P * P) (B * P)
  have e3 := LinearMap.baseChange_mul (A := A) P P
  have e4 := LinearMap.baseChange_mul (A := A) B P
  have e5 : (ℓ • D).baseChange A = ℓ • D.baseChange A :=
    map_nsmul (LinearMap.baseChangeHom ℤ_[p] A ↥(TateModule p (ModularCurve.JH L H))
      ↥(TateModule p (ModularCurve.JH L H))) ℓ D
  have e6 := LinearMap.baseChange_zero (A := A) (M := ↥(TateModule p (ModularCurve.JH L H)))
    (N := ↥(TateModule p (ModularCurve.JH L H))) (R := ℤ_[p])
  simp only [e1, e2, e3, e4, e5, e6] at h1
  exact h1

end Tate
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice"

section Star

variable (L : ℕ) [NeZero L] (H : Subgroup (ZMod L)ˣ) (p : ℕ) (n b : ℕ)
  (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev Tor : Type :=
  ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar L H) (p ^ n))

@[nolint unusedArguments]
def TwTor (_δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ) : Type :=
  Fin b → Tor L H p n

scoped instance TwTor.instAddCommGroup : AddCommGroup (TwTor L H p n b δ) :=
  inferInstanceAs (AddCommGroup (Fin b → Tor L H p n))

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"
variable {L H p n} in
omit [NeZero L] in
theorem diamondHBar_smul_mem_torsion (d : (ZMod L)ˣ) (σ : Gal) (x : Tor L H p n) :
    ModularCurve.diamondHBar L H d (σ • (x : ModularCurve.JH L H)) ∈
      AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar L H) (p ^ n) := by
  have hx := AlgebraicCurve.Pic0.mem_torsion.mp x.2
  rw [AlgebraicCurve.Pic0.mem_torsion, ← map_zsmul, ModularCurve.galois_smul_pic0_def,
    ← AlgebraicCurve.SemilinearAut.smul_zsmul, hx]
  have h0 : ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField L H) σ •
      (0 : ModularCurve.JH L H) = 0 :=
    map_zero (DistribSMul.toAddMonoidHom (ModularCurve.JH L H)
      (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField L H) σ))
  rw [h0, map_zero]

scoped instance TwTor.instSMul : SMul Gal (TwTor L H p n b δ) :=
  ⟨fun σ x i => ⟨ModularCurve.diamondHBar L H (δ σ) (σ • ((x i : Tor L H p n) : ModularCurve.JH L H)),
    diamondHBar_smul_mem_torsion (δ σ) σ (x i)⟩⟩

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"
theorem TwTor.coe_smul_apply (σ : Gal) (x : TwTor L H p n b δ) (i : Fin b) :
    (((σ • x : TwTor L H p n b δ) i : Tor L H p n) : ModularCurve.JH L H) =
      ModularCurve.diamondHBar L H (δ σ) (σ • ((x i : Tor L H p n) : ModularCurve.JH L H)) := rfl

scoped instance TwTor.instDistribMulAction : DistribMulAction Gal (TwTor L H p n b δ) where
  one_smul x := by
    funext i; apply Subtype.ext
    rw [TwTor.coe_smul_apply, map_one, one_smul, diamondHBar_one]
  mul_smul σ τ x := by
    funext i; apply Subtype.ext
    rw [TwTor.coe_smul_apply, TwTor.coe_smul_apply, TwTor.coe_smul_apply, map_mul,
      ModularCurve.diamondHBar_mul, mul_smul, galois_smul_diamondHBar L H]
  smul_zero σ := by
    funext i; apply Subtype.ext
    rw [TwTor.coe_smul_apply]
    have h0 : σ • (0 : ModularCurve.JH L H) = 0 :=
      map_zero (DistribSMul.toAddMonoidHom (ModularCurve.JH L H) σ)
    exact (congrArg (ModularCurve.diamondHBar L H (δ σ)) h0).trans (map_zero _)
  smul_add σ x y := by
    funext i; apply Subtype.ext
    rw [TwTor.coe_smul_apply]
    show ModularCurve.diamondHBar L H (δ σ)
        (σ • (((x i : Tor L H p n) : ModularCurve.JH L H) + ((y i : Tor L H p n) : ModularCurve.JH L H))) =
      ModularCurve.diamondHBar L H (δ σ) (σ • ((x i : Tor L H p n) : ModularCurve.JH L H)) +
        ModularCurve.diamondHBar L H (δ σ) (σ • ((y i : Tor L H p n) : ModularCurve.JH L H))
    have hadd : σ • (((x i : Tor L H p n) : ModularCurve.JH L H) + ((y i : Tor L H p n) : ModularCurve.JH L H)) =
        σ • ((x i : Tor L H p n) : ModularCurve.JH L H) + σ • ((y i : Tor L H p n) : ModularCurve.JH L H) :=
      map_add (DistribSMul.toAddMonoidHom (ModularCurve.JH L H) σ) _ _
    rw [hadd, map_add]

p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"

noncomputable def star : Gal →* AddAut (Fin b → Tor L H p n) :=
  DistribMulAction.toAddAut' Gal (TwTor L H p n b δ)

theorem coe_star_apply (σ : Gal) (x : Fin b → Tor L H p n) (i : Fin b) :
    ((star L H p n b δ σ x i : Tor L H p n) : ModularCurve.JH L H) =
      ModularCurve.diamondHBar L H (δ σ) (σ • ((x i : Tor L H p n) : ModularCurve.JH L H)) := rfl

end Star
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"

section BaseChange

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A]
  {V : Type} [AddCommGroup V] [Module R V]

theorem baseChange_comm {P Q : Module.End R V} (h : P * Q = Q * P) :
    (P.baseChange A) ∘ₗ (Q.baseChange A) = (Q.baseChange A) ∘ₗ (P.baseChange A) := by
  show P.baseChange A * Q.baseChange A = Q.baseChange A * P.baseChange A
  rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h]

theorem exists_baseChange_sub_eq_smul (P : Module.End R V) (c : R)
    (hP : ∀ v : V, ∃ w : V, P v - v = c • w) (z : A ⊗[R] V) :
    ∃ w : A ⊗[R] V, P.baseChange A z - z = (algebraMap R A c) • w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a v =>
    obtain ⟨w, hw⟩ := hP v
    refine ⟨a ⊗ₜ w, ?_⟩
    rw [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub, hw, algebraMap_smul,
      TensorProduct.tmul_smul]
  | add x y hx hy =>
    obtain ⟨wx, hwx⟩ := hx
    obtain ⟨wy, hwy⟩ := hy
    exact ⟨wx + wy, by rw [map_add, add_sub_add_comm, hwx, hwy, smul_add]⟩

end BaseChange
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"

end A2Lattice
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"

namespace A2Lattice

section Structure

open IsLocalRing

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)

theorem isTorsionFree_padicInt [Algebra ℤ_[p] 𝒪] : Module.IsTorsionFree ℤ_[p] 𝒪 := by
  have hinj : Function.Injective (algebraMap ℤ_[p] 𝒪) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    have hspec := PadicInt.unitCoeff_spec hne
    rw [hspec, map_mul, map_pow, map_natCast] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact (PadicInt.unitCoeff hne).isUnit.map (algebraMap ℤ_[p] 𝒪) |>.ne_zero h
    · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h
  refine Module.IsTorsionFree.of_smul_eq_zero fun a x hax => ?_
  rw [Algebra.smul_def] at hax
  rcases mul_eq_zero.mp hax with h | h
  · exact Or.inl (hinj (by rw [h, map_zero]))
  · exact Or.inr h

theorem isTorsionFree_H1 (L : ℕ) (H : Subgroup (ZMod L)ˣ) :
    Module.IsTorsionFree 𝒪 (CohCarrier.H1 L H 𝒪) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun a φ h => ?_
  by_cases ha : a = 0
  · exact Or.inl ha
  · refine Or.inr ?_
    ext γ
    have := congrArg (fun ψ : CohCarrier.H1 L H 𝒪 => ψ γ) h
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.zero_apply, smul_eq_mul, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact absurd h1 ha
    · exact h1

end Structure
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"

end A2Lattice
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"

section Main

open Polynomial IsLocalRing CuspForm.TWLevel TensorProduct A2Lattice

set_option hygiene false in
local notation "TT" => HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc

set_option hygiene false in
local notation "MM" => ML N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ

set_option hygiene false in
local notation "LL" => level N r qv

set_option hygiene false in
local notation "HH" => HQ N r qv p πΔ

set_option hygiene false in
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

set_option hygiene false in
local notation "Tor" n => ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
  (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))

set_option hygiene false in
local notation "Ta" => ↥(TateModule p (ModularCurve.JH (level N r qv) (HQ N r qv p πΔ)))

set_option hygiene false in
local notation "WW" => 𝒪 ⊗[ℤ_[p]] ↥(TateModule p (ModularCurve.JH (level N r qv) (HQ N r qv p πΔ)))

set_option hygiene false in
local notation "bcO[" P "]" => LinearMap.baseChange 𝒪 P

set_option hygiene false in
local notation "TaT[" ℓ ", " hℓ ", " hℓS ", " hℓL "]" =>
  A2Lattice.tateT (level N r qv) (HQ N r qv p πΔ) (↑S : Set ℕ) p ℓ hℓ hℓS hℓL

set_option hygiene false in
local notation "TaD[" d "]" => A2Lattice.tateDia (level N r qv) (HQ N r qv p πΔ) (↑S : Set ℕ) p d

set_option hygiene false in
local notation "TaG[" σ "]" => A2Lattice.tateGal (level N r qv) (HQ N r qv p πΔ) p σ

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 32000000 in
theorem A2Lattice.main
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
    (hpL : ¬ p ∣ level N r qv) :
    ∃ (b : ℕ) (δ : Gal →* (ZMod (level N r qv))ˣ),
      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, δ σ = 1) ∧
      GaloisFactorsThroughFiniteLevel δ ∧
      ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module TT Y) (_ : Module 𝒪 Y) (_ : IsScalarTower 𝒪 TT Y)
        (_ : Module.Finite 𝒪 Y) (_ : Module.IsTorsionFree 𝒪 Y)
        (ρY : Gal →* Module.End TT Y) (D : (ZMod (level N r qv))ˣ →* Module.End TT Y),
        (∀ x : TT, (∀ y : Y, x • y = 0) → x = 0) ∧
        (∀ (u : (ZMod (level N r qv))ˣ) (σ : Gal), D u * ρY σ = ρY σ * D u) ∧
        (∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ σ : Gal, (∀ x ∈ F, σ x = x) →
            ∀ y : Y, ρY σ y - y ∈ (Ideal.span {(p : TT)} ^ n • (⊤ : Submodule TT Y))) ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ level N r qv), ℓ ≠ p →
          ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
            ∀ σ : Gal, P.IsFrobeniusAt σ ℓ →
              ρY σ * ρY σ
                - (HeckeRing.T N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc ℓ hℓ hℓS hℓL) • ρY σ
                + (ℓ : TT) • D (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)) = 0) ∧
        (∀ n : ℕ,
          ∃ (star : Gal →* AddAut (Fin b → Tor n)),
            (∀ (σ : Gal) (x : Fin b → Tor n) (i : Fin b),
              ((star σ x i : Tor n) : ModularCurve.JH LL HH) =
                ModularCurve.diamondHBar LL HH (δ σ) (σ • ((x i : Tor n) : ModularCurve.JH LL HH))) ∧
            ∃ ι : Y →+ (Fin b → Tor n),
              (∀ y : Y, ι y = 0 ↔ y ∈ (Ideal.span {(p : TT)} ^ n • (⊤ : Submodule TT Y))) ∧
              ∀ (σ : Gal) (y : Y), ι (ρY σ y) = star σ (ι y)) := by

  letI : Algebra ℤ_[p] 𝒪 := (GaloisRep.padicIntToRing 𝒪 p hp𝒪).toAlgebra
  haveI : Module.Finite ℤ_[p] 𝒪 :=
    RibetIrr.module_finite_padicInt_of_isDiscreteValuationRing p 𝒪 hp𝒪
  haveI : Module.IsTorsionFree ℤ_[p] 𝒪 := isTorsionFree_padicInt p
  haveI : Module.Free ℤ_[p] 𝒪 := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite 𝒪 (CohCarrier.H1 LL HH 𝒪) := CohCarrier.H1_moduleFinite LL HH 𝒪 𝒪
  haveI : Module.IsTorsionFree 𝒪 (CohCarrier.H1 LL HH 𝒪) := isTorsionFree_H1 LL HH
  haveI : Module.Free 𝒪 (CohCarrier.H1 LL HH 𝒪) := Module.free_of_finite_type_torsion_free'
  have hres : Function.Surjective (algebraMap 𝒪 (ResidueField 𝒪)) := by
    rw [ResidueField.algebraMap_eq]; exact residue_surjective
  obtain ⟨hMLfin, hMLfree⟩ := CohCarrier.HeckeData.finite_ML_and_free_ML hres
    (heckeData N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ)
  haveI : Module.Finite 𝒪 MM := hMLfin
  haveI : Module.Free 𝒪 MM := hMLfree inferInstance

  let act : TT →ₐ[𝒪] Module.End 𝒪 MM := HeckeRing.act N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc
  have hfaith : ∀ x : TT, (∀ y : DualLattice act, x • y = 0) → x = 0 :=
    fun x hx => DualLattice.eq_zero_of_forall_smul_eq_zero act
      (HeckeRing.act_injective N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc) x hx

  have hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ LL),
      ℓ ≡ 1 [MOD LL] ∧
      θ (CuspForm.heckeAlgebra.T hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS) ≠
        (ℓ : ResidueField 𝒪) + 1 := by

    have hM₀ : 0 < LL * ∏ q ∈ S, max q 1 :=
      Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _))
        (Finset.prod_pos fun q _ => lt_max_of_lt_right Nat.one_pos)
    obtain ⟨ℓ, A, σ, hℓ, hℓM, hℓ1, hA, hσ, hev⟩ :=
      ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
        ρbar habs LL hM₀
    have hℓL : ¬ ℓ ∣ LL := fun h => hℓM (h.mul_right _)
    have hℓS : ℓ ∉ (↑S : Set ℕ) := by
      intro hmem
      apply hℓM
      refine Dvd.dvd.mul_left ?_ _
      have : ℓ ∣ max ℓ 1 := by rw [max_eq_left hℓ.one_lt.le]
      exact this.trans (Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp hmem))
    refine ⟨ℓ, hℓ, hℓS, hℓL, hℓ1, ?_⟩
    intro hEq
    apply hev
    rw [hθ ℓ hℓ (not_dvd_of_not_dvd_level N r qv hℓL) hℓS A hA σ hσ, hEq]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C]
    ring
  obtain ⟨E, hEE, hET₀, -, hEd₀, hEσ₀, Θ₀, hΘinj, hΘrange, hΘT₀, -, hΘd₀⟩ :=
    CuspForm.TWLevel.exists_heckeEquivariant_dual_ML_range_eq_idempotent_baseChange_tateModule_jH
      p hp𝒪 (↑S : Set ℕ) N r θ qv (fun i => (hqv i).1) α HH hcQ hdc hEis

  obtain ⟨δ, hδunr, hδfin, ρ', hρ'₀, hES₀⟩ :=
    ModularCurve.exists_character_frobeniusQuadratic_diamondTwist_tateModule_jH LL p HH (↑S : Set ℕ)

  have hET : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ LL),
      E ∘ₗ bcO[TaT[ℓ, hℓ, hℓS, hℓL]] = bcO[TaT[ℓ, hℓ, hℓS, hℓL]] ∘ₗ E := by
    intro ℓ hℓ hℓS hℓL; rw [tateT_def]; exact hET₀ ℓ hℓ hℓS hℓL
  have hEd : ∀ d : (ZMod LL)ˣ, E ∘ₗ bcO[TaD[d]] = bcO[TaD[d]] ∘ₗ E := by
    intro d; rw [tateDia_def]; exact hEd₀ d
  have hEσ : ∀ σ : Gal, E ∘ₗ bcO[TaG[σ]] = bcO[TaG[σ]] ∘ₗ E := by
    intro σ; rw [tateGal_def]; exact hEσ₀ σ
  have hΘT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ LL) (y : Module.Dual 𝒪 MM),
      Θ₀ (y ∘ₗ opML N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ (MvPolynomial.X (Gen.T ℓ hℓ hℓS hℓL))) =
        bcO[TaT[ℓ, hℓ, hℓS, hℓL]] (Θ₀ y) := by
    intro ℓ hℓ hℓS hℓL y; rw [tateT_def]; exact hΘT₀ ℓ hℓ hℓS hℓL y
  have hΘd : ∀ (u : (ZMod LL)ˣ) (y : Module.Dual 𝒪 MM),
      Θ₀ (y ∘ₗ diaML N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc u) = bcO[TaD[u]] (Θ₀ y) := by
    intro u y; rw [tateDia_def]; exact hΘd₀ u y
  have hρ' : ∀ σ : Gal, ρ' σ = TaD[δ σ] * TaG[σ] := by
    intro σ; rw [tateDia_def, tateGal_def]; exact hρ'₀ σ
  have hES : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ LL), ℓ ≠ p →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ (σ : Gal), A.IsFrobeniusAt σ ℓ → ∀ x : Ta,
          ρ' σ (ρ' σ x) - TaT[ℓ, hℓ, hℓS, hℓL] (ρ' σ x) +
            ℓ • TaD[ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)] x = 0 := by
    intro ℓ hℓ hℓS hℓL hℓp A hA σ hσ x
    rw [tateT_def, tateDia_def]
    exact hES₀ ℓ hℓ hℓS hℓL hℓp A hA σ hσ x
  clear hET₀ hEd₀ hEσ₀ hΘT₀ hΘd₀ hρ'₀ hES₀

  let Θ : DualLattice act →ₗ[𝒪] WW := Θ₀ ∘ₗ (DualLattice.toDual act).toLinearMap
  have hΘ : ∀ y, Θ y = Θ₀ (DualLattice.toDual act y) := fun _ => rfl
  have hSE : IsSummandEmbedding Θ E :=
    { injective := fun y y' h => DualLattice.toDual_injective act (hΘinj h)
      idem := hEE
      range_eq := by
        rw [← hΘrange]
        apply le_antisymm
        · rintro _ ⟨y, rfl⟩; exact ⟨DualLattice.toDual act y, rfl⟩
        · rintro _ ⟨y, rfl⟩; exact ⟨DualLattice.ofDual act y, rfl⟩ }

  have hintT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ LL) (y : DualLattice act),
      Θ (DualLattice.smulEnd act (HeckeRing.T N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc ℓ hℓ hℓS hℓL) y) =
        bcO[TaT[ℓ, hℓ, hℓS, hℓL]] (Θ y) := by
    intro ℓ hℓ hℓS hℓL y
    rw [DualLattice.smulEnd_apply, hΘ, hΘ, DualLattice.toDual_smul]
    exact hΘT ℓ hℓ hℓS hℓL _
  have hintD : ∀ (u : (ZMod LL)ˣ) (hu : u ∈ HR N r qv) (y : DualLattice act),
      Θ (DualLattice.smulEnd act (HeckeRing.diamond N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc u hu) y) =
        bcO[TaD[u]] (Θ y) := by
    intro u hu y
    rw [DualLattice.smulEnd_apply, hΘ, hΘ, DualLattice.toDual_smul]
    exact hΘd u _

  let G : Set TT := {x | act x ∈ heckeRingGens N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc}
  have hG : ∀ x : TT, x ∈ G ↔ act x ∈ heckeRingGens N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc :=
    fun _ => Iff.rfl
  have hgen : ∀ P : TT → Prop, (∀ g ∈ G, P g) → (∀ c : 𝒪, P (algebraMap 𝒪 TT c)) →
      (∀ x y, P x → P y → P (x + y)) → (∀ x y, P x → P y → P (x * y)) → ∀ x, P x := by
    intro P hPG hC hadd hmul x
    obtain ⟨a, ha⟩ := x
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact hPG ⟨a, _⟩ ha
    | algebraMap c => exact hC c
    | add a a' ha ha' iha iha' => exact hadd ⟨a, ha⟩ ⟨a', ha'⟩ iha iha'
    | mul a a' ha ha' iha iha' => exact hmul ⟨a, ha⟩ ⟨a', ha'⟩ iha iha'

  have hlin : ∀ (P : Module.End ℤ_[p] Ta),
      E ∘ₗ bcO[P] = bcO[P] ∘ₗ E →
      (∀ ℓ hℓ hℓS hℓL, P * TaT[ℓ, hℓ, hℓS, hℓL] = TaT[ℓ, hℓ, hℓS, hℓL] * P) →
      (∀ u : (ZMod LL)ˣ, P * TaD[u] = TaD[u] * P) →
      ∀ g ∈ G, ∀ y : DualLattice act, hSE.tr bcO[P] (g • y) = g • hSE.tr bcO[P] y := by
    intro P hPE hPT hPD g hg y
    rw [hG] at hg
    rcases hg with ⟨ℓ, hℓ, hℓS, hℓL, hgT⟩ | ⟨u, hu, hgD⟩
    · have hg' : g = HeckeRing.T N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc ℓ hℓ hℓS hℓL :=
        HeckeRing.ext N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc hgT
      subst hg'
      have := hSE.tr_comm_of_intertwine (fun y => hintT ℓ hℓ hℓS hℓL y) hPE (baseChange_comm (hPT ℓ hℓ hℓS hℓL)) y
      rwa [DualLattice.smulEnd_apply, DualLattice.smulEnd_apply] at this
    · have hg' : g = HeckeRing.diamond N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc u hu :=
        HeckeRing.ext N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc hgD
      subst hg'
      have := hSE.tr_comm_of_intertwine (fun y => hintD u hu y) hPE (baseChange_comm (hPD u)) y
      rwa [DualLattice.smulEnd_apply, DualLattice.smulEnd_apply] at this

  have hE_mul : ∀ P Q : Module.End ℤ_[p] Ta,
      E ∘ₗ bcO[P] = bcO[P] ∘ₗ E → E ∘ₗ bcO[Q] = bcO[Q] ∘ₗ E → E ∘ₗ bcO[P * Q] = bcO[P * Q] ∘ₗ E := by
    intro P Q hP hQ
    rw [LinearMap.baseChange_mul P Q]
    exact comp_mul_of_comp_eq hP hQ

  have hρ'T : ∀ σ ℓ hℓ hℓS hℓL, ρ' σ * TaT[ℓ, hℓ, hℓS, hℓL] = TaT[ℓ, hℓ, hℓS, hℓL] * ρ' σ :=
    fun σ ℓ hℓ hℓS hℓL => twist_mul_tateT LL HH (↑S : Set ℕ) p ρ' δ hρ' σ ℓ hℓ hℓS hℓL
  have hρ'D : ∀ σ (u : (ZMod LL)ˣ), ρ' σ * TaD[u] = TaD[u] * ρ' σ :=
    fun σ u => twist_mul_tateDia LL HH (↑S : Set ℕ) p ρ' δ hρ' σ u
  have hE_ρ' : ∀ σ, E ∘ₗ bcO[ρ' σ] = bcO[ρ' σ] ∘ₗ E := by
    intro σ
    rw [hρ']
    exact hE_mul _ _ (hEd (δ σ)) (hEσ σ)
  have hTD : ∀ (u : (ZMod LL)ˣ) ℓ hℓ hℓS hℓL,
      TaD[u] * TaT[ℓ, hℓ, hℓS, hℓL] = TaT[ℓ, hℓ, hℓS, hℓL] * TaD[u] :=
    fun u ℓ hℓ hℓS hℓL => (tateT_mul_tateDia LL HH (↑S : Set ℕ) p ℓ hℓ hℓS hℓL u).symm
  have hDD : ∀ u v : (ZMod LL)ˣ, TaD[u] * TaD[v] = TaD[v] * TaD[u] :=
    fun u v => tateDia_comm LL HH (↑S : Set ℕ) p u v

  let bcHom : Module.End ℤ_[p] Ta →* Module.End 𝒪 WW :=
    (Module.End.baseChangeHom ℤ_[p] 𝒪 Ta).toMonoidHom
  have hbcHom : ∀ P, bcHom P = bcO[P] := fun _ => rfl

  let ρW : Gal →* Module.End 𝒪 WW := bcHom.comp ρ'
  have hρWmem : ∀ σ, ρW σ ∈ commSubmonoid E := fun σ => hE_ρ' σ
  let ρYO : Gal →* Module.End 𝒪 (DualLattice act) := hSE.trHom.comp (ρW.codRestrict _ hρWmem)
  have hρYO : ∀ σ y, ρYO σ y = hSE.tr bcO[ρ' σ] y := fun _ _ => rfl
  let ρY : Gal →* Module.End TT (DualLattice act) :=
    liftHomOfGenerators G hgen ρYO (fun σ => hlin (ρ' σ) (hE_ρ' σ) (hρ'T σ) (hρ'D σ))
  have hρY : ∀ σ y, ρY σ y = hSE.tr bcO[ρ' σ] y := fun _ _ => rfl

  let DW : (ZMod LL)ˣ →* Module.End 𝒪 WW := bcHom.comp (A2Lattice.tateDia LL HH (↑S : Set ℕ) p)
  have hDWmem : ∀ u, DW u ∈ commSubmonoid E := fun u => hEd u
  let DO : (ZMod LL)ˣ →* Module.End 𝒪 (DualLattice act) := hSE.trHom.comp (DW.codRestrict _ hDWmem)
  let D : (ZMod LL)ˣ →* Module.End TT (DualLattice act) :=
    liftHomOfGenerators G hgen DO
      (fun u => hlin TaD[u] (hEd u) (fun ℓ hℓ hℓS hℓL => hTD u ℓ hℓ hℓS hℓL) (fun v => hDD u v))
  have hD : ∀ u y, D u y = hSE.tr bcO[TaD[u]] y := fun _ _ => rfl

  refine ⟨Module.finrank ℤ_[p] 𝒪, δ, hδunr p Fact.out hpL, hδfin, ?_⟩
  refine ⟨DualLattice act, DualLattice.instAddCommGroup act, DualLattice.instModuleT act,
    DualLattice.instModule act, DualLattice.instIsScalarTower act, DualLattice.instFinite act,
    DualLattice.instIsTorsionFree act, ?_⟩
  refine ⟨ρY, D, ?_⟩
  refine ⟨hfaith, ?_, ?_, ?_, ?_⟩
  ·
    intro u σ
    have hcomm : bcO[TaD[u]] * bcO[ρ' σ] = bcO[ρ' σ] * bcO[TaD[u]] := by
      rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, hρ'D σ u]
    refine LinearMap.ext fun y => ?_
    show hSE.tr bcO[TaD[u]] (hSE.tr bcO[ρ' σ] y) = hSE.tr bcO[ρ' σ] (hSE.tr bcO[TaD[u]] y)
    exact hSE.tr_comm_apply (hEd u) (hE_ρ' σ) hcomm y
  ·
    intro n
    obtain ⟨L₁, hL₁fin, hL₁⟩ :=
      ModularCurve.JH.exists_finiteDimensional_smul_eq_self_of_torsion LL HH (p ^ n)
        (pow_pos (Fact.out : p.Prime).pos n)
    obtain ⟨K, hKfin, hK⟩ := hδfin
    obtain ⟨lam, hlamker, hlamnat⟩ :=
      TateModule.exists_baseChange_pi_torsionBy_ker_eq_pow_smul p (ModularCurve.JH LL HH) 𝒪 n
    haveI := hL₁fin; haveI := hKfin
    refine ⟨L₁ ⊔ K, IntermediateField.finiteDimensional_sup L₁ K, ?_⟩
    intro σ hσ y
    have hσ₁ : ∀ x ∈ L₁, σ x = x := fun x hx => hσ x ((le_sup_left : L₁ ≤ L₁ ⊔ K) hx)
    have hσK : ∀ x ∈ K, σ x = x := fun x hx => hσ x ((le_sup_right : K ≤ L₁ ⊔ K) hx)
    have hδσ : δ σ = 1 := hK σ hσK
    have hρ'σ : ρ' σ = TaG[σ] := twist_eq_of_eq_one LL HH (↑S : Set ℕ) p ρ' δ hρ' σ hδσ

    have hdiv : ∀ z : WW, ∃ w : WW, bcO[ρ' σ] z - z = ((p : 𝒪) ^ n) • w := by
      intro z
      have hz : lam (bcO[ρ' σ] z - z) = 0 := by
        rw [map_sub, sub_eq_zero]
        funext i; apply Subtype.ext
        rw [hρ'σ, ← rep_gal_eq, hlamnat Gal σ z i]
        exact hL₁ σ hσ₁ _ ((Submodule.mem_torsionBy_iff _ _).mp (lam z i).2)
      exact (hlamker _).mp hz
    obtain ⟨y', hy'⟩ := hSE.exists_tr_sub_eq_smul (hE_ρ' σ) ((p : 𝒪) ^ n) hdiv y
    show hSE.tr bcO[ρ' σ] y - y ∈ _
    rw [DualLattice.mem_span_pow_smul_top_iff]
    exact ⟨y', hy'⟩
  ·
    intro ℓ hℓ hℓS hℓL hℓp P hP σ hσ

    have hW := baseChange_quadratic LL HH p (A := 𝒪) (ρ' σ) TaT[ℓ, hℓ, hℓS, hℓL]
      TaD[ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)] ℓ
      (hES ℓ hℓ hℓS hℓL hℓp P hP σ hσ)

    have hY := hSE.tr_quadratic_apply (hE_ρ' σ) ℓ hW

    have htrT : ∀ z : DualLattice act, hSE.tr bcO[TaT[ℓ, hℓ, hℓS, hℓL]] z =
        HeckeRing.T N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc ℓ hℓ hℓS hℓL • z := fun z =>
      congrArg (fun f : Module.End 𝒪 (DualLattice act) => f z)
        (hSE.tr_eq_of_intertwine (fun y => hintT ℓ hℓ hℓS hℓL y) (hET ℓ hℓ hℓS hℓL))
    refine LinearMap.ext fun y => ?_
    show hSE.tr bcO[ρ' σ] (hSE.tr bcO[ρ' σ] y)
        - HeckeRing.T N r qv (↑S : Set ℕ) 𝒪 HH θ α hcQ hdc ℓ hℓ hℓS hℓL • hSE.tr bcO[ρ' σ] y
        + (ℓ : TT) • hSE.tr bcO[TaD[ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)]] y
        = 0
    simp only [Nat.cast_smul_eq_nsmul, ← htrT]
    exact hY y
  ·
    intro n
    obtain ⟨lam, hlamker, hlamnat⟩ :=
      TateModule.exists_baseChange_pi_torsionBy_ker_eq_pow_smul p (ModularCurve.JH LL HH) 𝒪 n
    refine ⟨star LL HH p n (Module.finrank ℤ_[p] 𝒪) δ, fun σ x i => rfl, ?_⟩

    have hmem : ∀ (y : DualLattice act) (i : Fin (Module.finrank ℤ_[p] 𝒪)),
        ((lam (Θ y) i : ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) :
            ModularCurve.JH LL HH) ∈
          AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar LL HH)
            (p ^ n) :=
      fun y i => AlgebraicCurve.Pic0.mem_torsion.mpr
        ((Submodule.mem_torsionBy_iff _ _).mp (lam (Θ y) i).2)
    let ιfun : DualLattice act → (Fin (Module.finrank ℤ_[p] 𝒪) → Tor n) := fun y i => ⟨_, hmem y i⟩
    have hιfun : ∀ y i, ((ιfun y i : Tor n) : ModularCurve.JH LL HH) =
        ((lam (Θ y) i : ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) :
          ModularCurve.JH LL HH) := fun _ _ => rfl
    let ι : DualLattice act →+ (Fin (Module.finrank ℤ_[p] 𝒪) → Tor n) :=
      { toFun := ιfun
        map_zero' := by
          funext i; apply Subtype.ext
          rw [hιfun, show Θ 0 = 0 from map_zero Θ, show lam 0 = 0 from map_zero lam]; rfl
        map_add' := fun y y' => by
          funext i; apply Subtype.ext
          rw [hιfun, show Θ (y + y') = Θ y + Θ y' from map_add Θ y y',
            show lam (Θ y + Θ y') = lam (Θ y) + lam (Θ y') from map_add lam _ _]; rfl }
    have hι : ∀ y i, ((ι y i : Tor n) : ModularCurve.JH LL HH) =
        ((lam (Θ y) i : ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) :
          ModularCurve.JH LL HH) := fun _ _ => rfl
    refine ⟨ι, fun y => ?_, fun σ y => ?_⟩
    ·
      rw [DualLattice.mem_span_pow_smul_top_iff, hSE.exists_eq_smul_iff, ← hlamker]
      constructor
      · intro h
        funext i; apply Subtype.ext
        have := congrArg (fun x : Fin _ → Tor n => ((x i : Tor n) : ModularCurve.JH LL HH)) h
        simp only [hι] at this
        exact this
      · intro h
        funext i; apply Subtype.ext
        rw [hι, h]; rfl
    ·
      have hΘρ : Θ (hSE.tr bcO[ρ' σ] y) = bcO[TaD[δ σ]] (bcO[TaG[σ]] (Θ y)) := by
        rw [hSE.Θ_tr_of_comm (hE_ρ' σ), hρ', LinearMap.baseChange_mul TaD[δ σ] TaG[σ],
          Module.End.mul_apply bcO[TaD[δ σ]] bcO[TaG[σ]] (Θ y)]
      funext i; apply Subtype.ext
      have h2 : ((lam (bcO[TaG[σ]] (Θ y)) i :
            ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) : ModularCurve.JH LL HH) =
          σ • ((lam (Θ y) i : ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) :
            ModularCurve.JH LL HH) := by
        rw [← rep_gal_eq]; exact hlamnat Gal σ (Θ y) i
      have h1 : ((lam (bcO[TaD[δ σ]] (bcO[TaG[σ]] (Θ y))) i :
            ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) : ModularCurve.JH LL HH) =
          ModularCurve.diamondHBar LL HH (δ σ) ((lam (bcO[TaG[σ]] (Θ y)) i :
            ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) : ModularCurve.JH LL HH) := by
        rw [← rep_dia_eq]
        exact hlamnat (AddMonoid.End (ModularCurve.JH LL HH))
          (ModularCurve.genOpH LL HH (↑S : Set ℕ) (CohCarrier.Gen.dia (δ σ))) _ i
      show ((lam (Θ (hSE.tr bcO[ρ' σ] y)) i :
            ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) : ModularCurve.JH LL HH) =
          ModularCurve.diamondHBar LL HH (δ σ) (σ • ((lam (Θ y) i :
            ↥(Submodule.torsionBy ℤ (ModularCurve.JH LL HH) ((p ^ n : ℕ) : ℤ))) : ModularCurve.JH LL HH))
      rw [hΘρ, h1, h2]

end Main
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Polynomial IsLocalRing CuspForm.TWLevel

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

    (hpL : ¬ p ∣ level N r qv) :
    ∃ (b : ℕ) (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod (level N r qv))ˣ),

      (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, δ σ = 1) ∧

      GaloisFactorsThroughFiniteLevel δ ∧
      ∃ (Y : Type) (_ : AddCommGroup Y)
        (_ : Module (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) Y)
        (_ : Module 𝒪 Y)
        (_ : IsScalarTower 𝒪 (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) Y)
        (_ : Module.Finite 𝒪 Y) (_ : Module.IsTorsionFree 𝒪 Y)
        (ρY : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
          Module.End (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) Y)
        (D : (ZMod (level N r qv))ˣ →*
          Module.End (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) Y),

        (∀ x : HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc,
          (∀ y : Y, x • y = 0) → x = 0) ∧

        (∀ (u : (ZMod (level N r qv))ˣ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          D u * ρY σ = ρY σ * D u) ∧

        (∀ n : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, σ x = x) →
            ∀ y : Y, ρY σ y - y ∈
              (Ideal.span {(p : HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)} ^ n •
                (⊤ : Submodule (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) Y))) ∧

        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ level N r qv), ℓ ≠ p →
          ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
              ρY σ * ρY σ
                - (HeckeRing.T N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc ℓ hℓ hℓS hℓL) • ρY σ
                + (ℓ : HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) •
                    D (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓL)) = 0) ∧

        (∀ n : ℕ,
          ∃ (star : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
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
            ∃ ι : Y →+ (Fin b → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
                (ModularCurve.xHFunctionFieldBar (level N r qv) (HQ N r qv p πΔ)) (p ^ n))),
              (∀ y : Y, ι y = 0 ↔ y ∈
                (Ideal.span {(p : HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc)} ^ n •
                  (⊤ : Submodule (HeckeRing N r qv (↑S : Set ℕ) 𝒪 (HQ N r qv p πΔ) θ α hcQ hdc) Y))) ∧
              ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : Y),
                ι (ρY σ y) = star σ (ι y)) :=
  A2Lattice.main p hp𝒪 ρbar habs S N hNS r hr hrN θ hθ t qv hqinj hqv hqr πΔ α hcQ hdc hpL

end
p2m_reactivate "P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.DualLattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.IsSummandEmbedding P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level.A2Lattice.TwTor"

end S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level
end P2MW
export P2MW.S_CuspForm_TWLevel_HeckeRing_exists_finiteLevel_faithful_galoisHeckeLattice_frobenius_torsionEmbedding_jH_of_not_dvd_level (solution)

-- Prove2me | solution 1 for CuspForm.exists_padicGaloisModule_heckeRingH_two_frobenius_relation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/733fce52-7c23-55bf-8e58-c212d9a34ef5

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_PeriodOf
import Theorems.Thm_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
import Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jH
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Theorems.Thm_ModularCurve_JH_exists_finiteDimensional_smul_eq_self_of_torsion
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU
import Theorems.Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
import Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import Theorems.Thm_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_diamondRaw_comm
import Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_padicGaloisModule_heckeRingH_two_frobenius_relation
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule"
p2m_attr_erase "instance" "KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply ModularCurve.coe_laurentReductionDegZero ModularCurve.laurentReductionDiv_apply ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun"
p2m_attr_erase "simp" "KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups TensorProduct ModularForm
open CongruenceSubgroup

namespace GalTwoAssembly

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H

abbrev V : Type := CuspForm (CohCarrier.GammaH M H) 2

abbrev PL : Submodule ℤ (Module.Dual ℂ (V M H)) := ModularCurve.periodLatticeOf (Gam M H)

abbrev TT : Subring (V M H →ₗ[ℂ] V M H) := CuspForm.heckeRingH M H 2

section Shortcuts

scoped instance (priority := high) instAddCommGroupV : AddCommGroup (V M H) := inferInstance
scoped instance (priority := high) instModuleV : Module ℂ (V M H) := inferInstance
scoped instance (priority := high) instAddCommGroupDualV : AddCommGroup (Module.Dual ℂ (V M H)) := inferInstance
scoped instance (priority := high) instModuleDualV : Module ℂ (Module.Dual ℂ (V M H)) := inferInstance
scoped instance (priority := high) instAddCommGroupPL : AddCommGroup (PL M H) := inferInstance
scoped instance (priority := high) instAddCommMonoidPL : AddCommMonoid (PL M H) := inferInstance
scoped instance (priority := high) instModulePL : Module ℤ (PL M H) := inferInstance
scoped instance (priority := high) instRingTT : Ring (TT M H) := inferInstance
scoped instance (priority := high) instSemiringTT : Semiring (TT M H) := inferInstance
scoped instance (priority := high) instNonAssocRingTT : NonAssocRing (TT M H) := inferInstance
scoped instance (priority := high) instNonUnitalNonAssocRingTT : NonUnitalNonAssocRing (TT M H) := inferInstance
scoped instance (priority := high) instNonUnitalRingTT : NonUnitalRing (TT M H) := inferInstance
scoped instance (priority := high) instNonAssocSemiringTT : NonAssocSemiring (TT M H) := inferInstance
scoped instance (priority := high) instNonUnitalNonAssocSemiringTT :
    NonUnitalNonAssocSemiring (TT M H) := inferInstance
scoped instance (priority := high) instNonUnitalSemiringTT : NonUnitalSemiring (TT M H) := inferInstance
scoped instance (priority := high) instAddCommGroupTT : AddCommGroup (TT M H) := inferInstance
scoped instance (priority := high) instAddCommMonoidTT : AddCommMonoid (TT M H) := inferInstance
scoped instance (priority := high) instAddGroupTT : AddGroup (TT M H) := inferInstance
scoped instance (priority := high) instAddMonoidTT : AddMonoid (TT M H) := inferInstance
scoped instance (priority := high) instMonoidTT : Monoid (TT M H) := inferInstance
scoped instance (priority := high) instMulOneClassTT : MulOneClass (TT M H) := inferInstance
scoped instance (priority := high) instMulZeroClassTT : MulZeroClass (TT M H) := inferInstance
scoped instance (priority := high) instAddMonoidWithOneTT : AddMonoidWithOne (TT M H) := inferInstance
scoped instance (priority := high) instAddGroupWithOneTT : AddGroupWithOne (TT M H) := inferInstance
scoped instance (priority := high) instMulTT : Mul (TT M H) := inferInstance
scoped instance (priority := high) instAddTT : Add (TT M H) := inferInstance
scoped instance (priority := high) instZeroTT : Zero (TT M H) := inferInstance
scoped instance (priority := high) instOneTT : One (TT M H) := inferInstance
scoped instance (priority := high) instNegTT : Neg (TT M H) := inferInstance
scoped instance (priority := high) instSubTT : Sub (TT M H) := inferInstance
scoped instance (priority := high) instModuleIntTT : Module ℤ (TT M H) := inferInstance

end Shortcuts

theorem isCong : IsCongruenceSubgroup (Gam M H) :=
  ⟨M, NeZero.ne M, CuspForm.Gamma_le_GammaH M H⟩

theorem periodOf_eq_pm (f : V M H) (δ : Gam M H) :
    ModularCurve.periodOf (Gam M H) δ f =
      ModularCurve.periodMapOf (Gam M H) f (Additive.ofMul δ) :=
  (ModularCurve.periodMapOf_apply_eq_periodOf (Gam M H) f δ).symm

theorem pm_injective : Function.Injective (ModularCurve.periodMapOf (Gam M H)) := by
  intro f g hfg
  have h0 : f - g = 0 := by
    apply ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero (Gam M H)
    intro γ
    rw [map_sub, periodOf_eq_pm, periodOf_eq_pm, hfg, sub_self, Complex.zero_re]
  exact sub_eq_zero.mp h0

theorem periodOf_mul (δ₁ δ₂ : Gam M H) :
    ModularCurve.periodOf (Gam M H) (δ₁ * δ₂) =
      ModularCurve.periodOf (Gam M H) δ₁ + ModularCurve.periodOf (Gam M H) δ₂ := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.add_apply, periodOf_eq_pm, periodOf_eq_pm, periodOf_eq_pm, ofMul_mul, map_add]

theorem periodOf_one : ModularCurve.periodOf (Gam M H) 1 = 0 := by
  apply LinearMap.ext
  intro f
  rw [periodOf_eq_pm, ofMul_one, map_zero, LinearMap.zero_apply]

theorem periodOf_eq_zero_of_trace (γ : Gam M H)
    (hγ : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    ModularCurve.periodOf (Gam M H) γ = 0 := by
  apply LinearMap.ext
  intro f
  rw [periodOf_eq_pm, LinearMap.zero_apply]
  exact ModularCurve.periodMapOf_mem_parabolicHoms (Gam M H) f γ hγ

def perHom : Additive (Gam M H) →+ PL M H where
  toFun a := ⟨ModularCurve.periodOf (Gam M H) (Additive.toMul a),
    ModularCurve.periodOf_mem_periodLatticeOf (Gam M H) _⟩
  map_zero' := Subtype.ext (by simp only [toMul_zero]; exact periodOf_one M H)
  map_add' a b := Subtype.ext (by simp only [toMul_add]; exact periodOf_mul M H _ _)

@[scoped simp] theorem perHom_ofMul (δ : Gam M H) :
    perHom M H (Additive.ofMul δ) =
      ⟨ModularCurve.periodOf (Gam M H) δ, ModularCurve.periodOf_mem_periodLatticeOf (Gam M H) δ⟩ :=
  rfl

theorem pm_heckeT {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : V M H) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMapOf (Gam M H) (CuspForm.heckeTLinH 2 hℓ hℓM f) =
      CohCarrier.heckeT M H ℓ ℂ (ModularCurve.periodMapOf (Gam M H) f) :=
  ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)) (CuspForm.gammaLift_apply_11 hℓ hℓM)
    f _ (CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f)

theorem pm_heckeU {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (f : V M H) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ModularCurve.periodMapOf (Gam M H) (CuspForm.heckeULinH 2 q f) =
      CohCarrier.heckeT M H q ℂ (ModularCurve.periodMapOf (Gam M H) f) :=
  ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU M H hq hqM f _
    (CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM) f)

theorem pm_diamond (d : (ZMod M)ˣ) (σ : Gamma0 M) (hσ : CohCarrier.gamma0Units M σ = d)
    (f : V M H) :
    ModularCurve.periodMapOf (Gam M H) (CuspForm.diamondLinH 2 d f) =
      CohCarrier.diamondRaw M H ℂ σ (ModularCurve.periodMapOf (Gam M H) f) :=
  ModularCurve.periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash M H σ f _
    (CuspForm.coe_diamondLinH_eq_slash 2 (CuspForm.stableD M H 2) d σ hσ f)

theorem exists_lift (ℓ : ℕ) [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, CohCarrier.gamma0Units M σ = d ∧
      ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0 := by
  haveI : NeZero (ℓ * M) := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne M)⟩
  have hdvd : M ∣ ℓ * M := dvd_mul_left M ℓ
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hdvd d
  obtain ⟨τ, hτ⟩ := CohCarrier.gamma0Units_surjective (ℓ * M) u
  have hτ10 : ((((τ : SL(2, ℤ)) 1 0 : ℤ)) : ZMod (ℓ * M)) = 0 := Gamma0_mem.mp τ.2
  have hdiv : ((ℓ * M : ℕ) : ℤ) ∣ (τ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hτ10
  have hσ0 : (τ : SL(2, ℤ)) ∈ Gamma0 M := by
    rw [Gamma0_mem]
    have hM : ((M : ℕ) : ℤ) ∣ (τ : SL(2, ℤ)) 1 0 :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) hdiv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hM
  refine ⟨⟨τ, hσ0⟩, ?_, hdiv⟩
  rw [← hu, ← hτ]
  ext
  rw [ZMod.unitsMap_def, Units.coe_map, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  simp [Gamma0Map]

theorem shadow_cases (g : CohCarrier.Gen M (∅ : Set ℕ)) :
    (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ∀ f : V M H,
        ModularCurve.periodMapOf (Gam M H) (CuspForm.heckeGenH (H := H) ∅ 2 g f) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            CohCarrier.heckeT M H ℓ ℂ (ModularCurve.periodMapOf (Gam M H) f))) ∨
    (∃ d : (ZMod M)ˣ, CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2 g = CuspForm.diamondLinH 2 d) := by
  cases g with
  | T ℓ hℓ hS hℓM => exact Or.inl ⟨ℓ, hℓ, fun f => pm_heckeT M H hℓ hℓM f⟩
  | U q hq hqM => exact Or.inl ⟨q, hq, fun f => pm_heckeU M H hq hqM f⟩
  | dia d => exact Or.inr ⟨d, rfl⟩

theorem gen_comm (g₁ g₂ : CohCarrier.Gen M (∅ : Set ℕ)) :
    CuspForm.heckeGenH (H := H) ∅ 2 g₁ * CuspForm.heckeGenH ∅ 2 g₂ =
      CuspForm.heckeGenH ∅ 2 g₂ * CuspForm.heckeGenH ∅ 2 g₁ := by
  apply LinearMap.ext
  intro f
  apply pm_injective M H
  simp only [Module.End.mul_apply]
  rcases shadow_cases M H g₁ with ⟨ℓ₁, hℓ₁, h₁⟩ | ⟨d₁, h₁⟩ <;>
    rcases shadow_cases M H g₂ with ⟨ℓ₂, hℓ₂, h₂⟩ | ⟨d₂, h₂⟩
  · haveI : NeZero ℓ₁ := ⟨hℓ₁.ne_zero⟩
    haveI : NeZero ℓ₂ := ⟨hℓ₂.ne_zero⟩
    rw [h₁, h₂, h₂, h₁]
    by_cases heq : ℓ₁ = ℓ₂
    · subst heq
      rfl
    · exact CohCarrier.heckeT_comm_of_prime M H ℓ₁ ℓ₂ hℓ₁
        ((Nat.coprime_primes hℓ₁ hℓ₂).mpr heq) _
  · haveI : NeZero ℓ₁ := ⟨hℓ₁.ne_zero⟩
    obtain ⟨σ, hσ, hdiv⟩ := exists_lift M ℓ₁ d₂
    rw [h₁, h₂, pm_diamond M H d₂ σ hσ, pm_diamond M H d₂ σ hσ, h₁]
    exact CohCarrier.heckeT_diamondRaw_comm M H ℓ₁ σ hdiv _
  · haveI : NeZero ℓ₂ := ⟨hℓ₂.ne_zero⟩
    obtain ⟨σ, hσ, hdiv⟩ := exists_lift M ℓ₂ d₁
    rw [h₁, h₂, pm_diamond M H d₁ σ hσ, pm_diamond M H d₁ σ hσ, h₂]
    exact (CohCarrier.heckeT_diamondRaw_comm M H ℓ₂ σ hdiv _).symm
  · rw [h₁, h₂, pm_diamond M H d₁ (CuspForm.gammaLift M d₁) (CuspForm.gamma0Units_gammaLift d₁),
      pm_diamond M H d₂ (CuspForm.gammaLift M d₂) (CuspForm.gamma0Units_gammaLift d₂),
      pm_diamond M H d₂ (CuspForm.gammaLift M d₂) (CuspForm.gamma0Units_gammaLift d₂),
      pm_diamond M H d₁ (CuspForm.gammaLift M d₁) (CuspForm.gamma0Units_gammaLift d₁)]
    exact CohCarrier.diamondRaw_comm M H _ _ _

theorem heckeRingH_le_centralizer :
    TT M H ≤ Subring.centralizer (Set.range (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2)) := by
  refine Subring.closure_le.mpr ?_
  rintro _ ⟨g₁, rfl⟩
  rw [SetLike.mem_coe, Subring.mem_centralizer_iff]
  rintro _ ⟨g₂, rfl⟩
  exact gen_comm M H g₂ g₁

theorem hecke_comm (s t : TT M H) : s * t = t * s := by
  have h1 : (t : V M H →ₗ[ℂ] V M H) ∈
      Subring.centralizer (Set.range (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2)) :=
    heckeRingH_le_centralizer M H t.2
  have h2 : TT M H ≤ Subring.centralizer {(t : V M H →ₗ[ℂ] V M H)} := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ((Subring.mem_centralizer_iff.mp h1) _ ⟨g, rfl⟩).symm
  have h3 := Subring.mem_centralizer_iff.mp (h2 s.2) _ (Set.mem_singleton _)
  exact Subtype.ext h3.symm

omit [NeZero M] in

theorem exists_heckeT_universal (ℓ : ℕ) [NeZero ℓ] (δ : Gam M H) :
    ∃ γ₀ : Gam M H, ∀ (A : Type) [AddCommGroup A] (φ : CohCarrier.H1 M H A),
      CohCarrier.heckeT M H ℓ A φ (Additive.ofMul δ) = φ (Additive.ofMul γ₀) := by
  let U : Type := Additive (Abelianization (Gam M H))
  let u : CohCarrier.H1 M H U := MonoidHom.toAdditive (Abelianization.of (G := Gam M H))
  obtain ⟨γ₀, hγ₀⟩ := (QuotientGroup.mk_surjective (s := commutator (Gam M H)))
    (Additive.toMul (CohCarrier.heckeT M H ℓ U u (Additive.ofMul δ)))
  refine ⟨γ₀, fun A _ φ => ?_⟩
  let φ' : U →+ A :=
    MonoidHom.toAdditiveLeft (Abelianization.lift (AddMonoidHom.toMultiplicativeRight φ))
  have hφ : φ = φ'.comp u := by
    ext a
    simp [φ', u, MonoidHom.toAdditiveLeft, AddMonoidHom.toMultiplicativeRight, MonoidHom.toAdditive]
  rw [hφ, CohCarrier.heckeT_comp_coeff M H ℓ φ' u, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply]
  congr 1
  change _ = Additive.ofMul (Abelianization.of γ₀)
  change _ = Additive.ofMul (QuotientGroup.mk γ₀)
  rw [hγ₀, ofMul_toMul]

theorem exists_gen_universal (g : CohCarrier.Gen M (∅ : Set ℕ)) (δ : Gam M H) :
    ∃ γ₀ : Gam M H,
      (∀ (A : Type) [CommRing A] (φ : CohCarrier.H1 M H A),
        CohCarrier.opFamily M H ∅ A g φ (Additive.ofMul δ) = φ (Additive.ofMul γ₀)) ∧
      ∀ f : V M H, ModularCurve.periodOf (Gam M H) δ (CuspForm.heckeGenH (H := H) ∅ 2 g f) =
        ModularCurve.periodOf (Gam M H) γ₀ f := by
  cases g with
  | T ℓ hℓ hS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨γ₀, h⟩ := exists_heckeT_universal M H ℓ δ
    refine ⟨γ₀, fun A _ φ => h A φ, fun f => ?_⟩
    rw [periodOf_eq_pm, periodOf_eq_pm, CuspForm.heckeGenH_T, pm_heckeT M H hℓ hℓM f]
    exact h ℂ _
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    obtain ⟨γ₀, h⟩ := exists_heckeT_universal M H q δ
    refine ⟨γ₀, fun A _ φ => h A φ, fun f => ?_⟩
    rw [periodOf_eq_pm, periodOf_eq_pm, CuspForm.heckeGenH_U, pm_heckeU M H hq hqM f]
    exact h ℂ _
  | dia d =>
    refine ⟨CohCarrier.conjHom M H (CuspForm.gammaLift M d) δ, fun A _ φ => rfl, fun f => ?_⟩
    rw [periodOf_eq_pm, periodOf_eq_pm, CuspForm.heckeGenH_dia,
      pm_diamond M H d (CuspForm.gammaLift M d) (CuspForm.gamma0Units_gammaLift d) f]
    rfl

theorem dualMap_gen_periodOf (g : CohCarrier.Gen M (∅ : Set ℕ)) (δ γ₀ : Gam M H)
    (h : ∀ f : V M H, ModularCurve.periodOf (Gam M H) δ (CuspForm.heckeGenH (H := H) ∅ 2 g f) =
        ModularCurve.periodOf (Gam M H) γ₀ f) :
    (CuspForm.heckeGenH (H := H) ∅ 2 g).dualMap (ModularCurve.periodOf (Gam M H) δ) =
      ModularCurve.periodOf (Gam M H) γ₀ :=
  LinearMap.ext fun f => by rw [LinearMap.dualMap_apply, h]

theorem dualMap_mem_of_mem {t : V M H →ₗ[ℂ] V M H} (ht : t ∈ TT M H)
    {v : Module.Dual ℂ (V M H)} (hv : v ∈ PL M H) : t.dualMap v ∈ PL M H := by
  have ht' : t ∈ Subring.closure (Set.range (CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2)) := ht
  clear ht
  induction ht' using Subring.closure_induction generalizing v with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨δ, rfl⟩ := hw
      obtain ⟨γ₀, -, hper⟩ := exists_gen_universal M H g δ
      rw [dualMap_gen_periodOf M H g δ γ₀ hper]
      exact ModularCurve.periodOf_mem_periodLatticeOf _ _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul n w _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ n ih
  | zero =>
    have : (0 : V M H →ₗ[ℂ] V M H).dualMap v = 0 := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact Submodule.zero_mem _
  | one =>
    have : (1 : V M H →ₗ[ℂ] V M H).dualMap v = v := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact hv
  | add x y _ _ hx hy =>
    have : (x + y).dualMap v = x.dualMap v + y.dualMap v := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact Submodule.add_mem _ (hx hv) (hy hv)
  | neg x _ hx =>
    have : (-x).dualMap v = -(x.dualMap v) := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact Submodule.neg_mem _ (hx hv)
  | mul x y _ _ hx hy =>
    have : (x * y).dualMap v = y.dualMap (x.dualMap v) := LinearMap.ext fun f => by
      simp [LinearMap.dualMap_apply]
    rw [this]; exact hy (hx hv)

def Pend (t : TT M H) : PL M H →ₗ[ℤ] PL M H where
  toFun v := ⟨(t : V M H →ₗ[ℂ] V M H).dualMap v, dualMap_mem_of_mem M H t.2 v.2⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' n v := Subtype.ext (by simp [map_zsmul])

theorem Pend_apply_apply (t : TT M H) (v : PL M H) (f : V M H) :
    ((Pend M H t v : PL M H) : Module.Dual ℂ (V M H)) f =
      (v : Module.Dual ℂ (V M H)) ((t : V M H →ₗ[ℂ] V M H) f) :=
  rfl

theorem Pend_one : Pend M H 1 = LinearMap.id :=
  LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)

theorem Pend_mul' (s t : TT M H) : Pend M H (s * t) = Pend M H t ∘ₗ Pend M H s :=
  LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)

theorem Pend_mul (s t : TT M H) : Pend M H (s * t) = Pend M H s ∘ₗ Pend M H t := by
  rw [hecke_comm M H s t, Pend_mul']

theorem Pend_add (s t : TT M H) : Pend M H (s + t) = Pend M H s + Pend M H t :=
  LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun f => by
    simp only [LinearMap.add_apply, Submodule.coe_add, Pend_apply_apply, Subring.coe_add, map_add])

theorem Pend_zero : Pend M H 0 = 0 :=
  LinearMap.ext fun v => Subtype.ext (LinearMap.ext fun f => by
    simp only [LinearMap.zero_apply, Submodule.coe_zero, Pend_apply_apply, Subring.coe_zero, map_zero])

def PendL : TT M H →ₗ[ℤ] (PL M H →ₗ[ℤ] PL M H) :=
  AddMonoidHom.toIntLinearMap
    { toFun := Pend M H
      map_zero' := Pend_zero M H
      map_add' := Pend_add M H }

@[scoped simp] theorem PendL_apply (t : TT M H) : PendL M H t = Pend M H t := rfl

theorem Pend_eq_zero (t : TT M H) (ht : Pend M H t = 0) : t = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  have hper : ∀ δ : Gam M H,
      ModularCurve.periodOf (Gam M H) δ ((t : V M H →ₗ[ℂ] V M H) f) = 0 := fun δ => by
    have := congrArg (fun P : PL M H →ₗ[ℤ] PL M H =>
      ((P ⟨ModularCurve.periodOf (Gam M H) δ, ModularCurve.periodOf_mem_periodLatticeOf _ δ⟩ :
        PL M H) : Module.Dual ℂ (V M H)) f) ht
    simpa [Pend_apply_apply] using this
  have h0 := ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero (Gam M H)
    ((t : V M H →ₗ[ℂ] V M H) f) (fun δ => by rw [hper δ, Complex.zero_re])
  simpa using h0

theorem PendL_injective : Function.Injective (PendL M H) := by
  intro s t hst
  have h : PendL M H (s - t) = 0 := by rw [map_sub, hst, sub_self]
  exact sub_eq_zero.mp (Pend_eq_zero M H _ h)

def PendRing : TT M H →+* Module.End ℤ (PL M H) where
  toFun := Pend M H
  map_one' := Pend_one M H
  map_mul' := Pend_mul M H
  map_zero' := Pend_zero M H
  map_add' := Pend_add M H

@[scoped simp] theorem PendRing_apply (t : TT M H) : PendRing M H t = Pend M H t := rfl

section BaseChange

variable {R A N : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup N] [Module R N]

theorem liftBaseChange_baseChangeHom_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R N) :
    Function.Injective ((LinearMap.baseChangeHom R A N N).liftBaseChange A) := by
  classical
  set κ := (LinearMap.baseChangeHom R A N N).liftBaseChange A
  let BR := Algebra.TensorProduct.basis A b.end
  let B' := (Algebra.TensorProduct.basis A b).end
  have hκ : κ = (BR.equiv B' (Equiv.refl _)).toLinearMap := by
    refine BR.ext (fun ij => ?_)
    rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply, Equiv.refl_apply]
    simp only [κ, BR, B', Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul,
      LinearMap.baseChangeHom_apply, one_smul, Module.Basis.baseChange_end]
  rw [hκ]
  exact (BR.equiv B' _).injective

theorem mul_eq_of_quadratic {S B : Type*} [CommRing S] [AddCommGroup B] [Module S B]
    (T D F : Module.End S B) (ℓ : ℕ) (h : ∀ x : B, D (F (F x)) - T (F x) + ℓ • x = 0) :
    T * F = D * (F * F) + (ℓ : S) • (1 : Module.End S B) := by
  apply LinearMap.ext
  intro x
  have hx := h x
  rw [sub_add_eq_add_sub, sub_eq_zero] at hx
  rw [Module.End.mul_apply, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply, Nat.cast_smul_eq_nsmul]
  exact hx.symm

end BaseChange

theorem commute_map_of_gen {E : Type*} [Ring E] (φ : TT M H →+* E) (r : E)
    (h : ∀ g : CohCarrier.Gen M (∅ : Set ℕ),
      r * φ ⟨CuspForm.heckeGenH (H := H) ∅ 2 g, CuspForm.heckeGenH_mem_heckeRingH ∅ 2 g⟩ =
        φ ⟨CuspForm.heckeGenH (H := H) ∅ 2 g, CuspForm.heckeGenH_mem_heckeRingH ∅ 2 g⟩ * r)
    (t : TT M H) : r * φ t = φ t * r := by
  obtain ⟨t, ht⟩ := t
  refine Subring.closure_induction (p := fun x hx => r * φ ⟨x, hx⟩ = φ ⟨x, hx⟩ * r)
    ?_ ?_ ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨g, rfl⟩
    exact h g
  · change r * φ 0 = φ 0 * r
    rw [map_zero, mul_zero, zero_mul]
  · change r * φ 1 = φ 1 * r
    rw [map_one, mul_one, one_mul]
  · intro x y hx hy ihx ihy
    change r * φ (⟨x, hx⟩ + ⟨y, hy⟩) = φ (⟨x, hx⟩ + ⟨y, hy⟩) * r
    rw [map_add, mul_add, add_mul, ihx, ihy]
  · intro x hx ih
    change r * φ (-⟨x, hx⟩) = φ (-⟨x, hx⟩) * r
    rw [map_neg, mul_neg, neg_mul, ih]
  · intro x y hx hy ihx ihy
    change r * φ (⟨x, hx⟩ * ⟨y, hy⟩) = φ (⟨x, hx⟩ * ⟨y, hy⟩) * r
    rw [map_mul, ← mul_assoc, ihx, mul_assoc, ihy, mul_assoc]

variable (p : ℕ) [Fact p.Prime]

scoped instance (priority := high) instAddCommGroupTateJH :
    AddCommGroup (TateModule p (ModularCurve.JH M H)) := inferInstance

scoped instance (priority := high) instAddCommMonoidTateJH :
    AddCommMonoid (TateModule p (ModularCurve.JH M H)) := inferInstance

scoped instance (priority := high) instModuleTateJH :
    Module ℤ_[p] (TateModule p (ModularCurve.JH M H)) := inferInstance

scoped instance (priority := high) instAddCommGroupTensorPL : AddCommGroup (ℤ_[p] ⊗[ℤ] PL M H) := inferInstance
scoped instance (priority := high) instAddCommMonoidTensorPL : AddCommMonoid (ℤ_[p] ⊗[ℤ] PL M H) :=
  inferInstance
scoped instance (priority := high) instModuleTensorPL : Module ℤ_[p] (ℤ_[p] ⊗[ℤ] PL M H) := inferInstance
scoped instance (priority := high) instModuleIntTensorPL : Module ℤ (ℤ_[p] ⊗[ℤ] PL M H) := inferInstance
scoped instance (priority := high) instRingEndTensorPL : Ring (Module.End ℤ_[p] (ℤ_[p] ⊗[ℤ] PL M H)) :=
  inferInstance
scoped instance (priority := high) instAddCommGroupEndTensorPL :
    AddCommGroup (Module.End ℤ_[p] (ℤ_[p] ⊗[ℤ] PL M H)) := inferInstance
scoped instance (priority := high) instModuleEndTensorPL :
    Module ℤ_[p] (Module.End ℤ_[p] (ℤ_[p] ⊗[ℤ] PL M H)) := inferInstance
scoped instance (priority := high) instRingEndTateJH :
    Ring (Module.End ℤ_[p] (TateModule p (ModularCurve.JH M H))) := inferInstance
scoped instance (priority := high) instAddCommGroupEndTateJH :
    AddCommGroup (Module.End ℤ_[p] (TateModule p (ModularCurve.JH M H))) := inferInstance
scoped instance (priority := high) instModuleEndTateJH :
    Module ℤ_[p] (Module.End ℤ_[p] (TateModule p (ModularCurve.JH M H))) := inferInstance

theorem sep {y z : ℤ_[p] ⊗[ℤ] PL M H}
    (h : ∀ χ : PL M H →ₗ[ℤ] ℤ_[p], χ.liftBaseChange ℤ_[p] y = χ.liftBaseChange ℤ_[p] z) :
    y = z := by
  classical
  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (Gam M H) (isCong M H)
  let bp := Algebra.TensorProduct.basis ℤ_[p] b
  refine bp.ext_elem (fun i => ?_)
  let χ : PL M H →ₗ[ℤ] ℤ_[p] := (Algebra.linearMap ℤ ℤ_[p]).comp (b.coord i)
  have hχ : χ.liftBaseChange ℤ_[p] = (Finsupp.lapply i) ∘ₗ (bp.repr : _ →ₗ[ℤ_[p]] _) := by
    refine bp.ext (fun j => ?_)
    simp only [bp, χ, Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul,
      LinearMap.coe_comp, Function.comp_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Algebra.linearMap_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply]
    rw [← Algebra.TensorProduct.basis_apply, Module.Basis.repr_self, Finsupp.single_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
  have h1 := h χ
  rw [hχ] at h1
  exact h1

theorem linearIndependent_baseChange_Pend {ι : Type*} (τ : Module.Basis ι ℤ (TT M H)) :
    LinearIndependent ℤ_[p] (fun k => (Pend M H (τ k)).baseChange ℤ_[p]) := by
  classical
  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (Gam M H) (isCong M H)
  have hker : LinearMap.ker (PendL M H) = ⊥ := LinearMap.ker_eq_bot.mpr (PendL_injective M H)
  have h1 : LinearIndependent ℤ (fun k => PendL M H (τ k)) := τ.linearIndependent.map' _ hker
  have h2 : LinearIndependent ℤ_[p] (fun k => (1 : ℤ_[p]) ⊗ₜ[ℤ] PendL M H (τ k)) :=
    Module.Flat.linearIndependent_one_tmul h1
  set κ := (LinearMap.baseChangeHom ℤ ℤ_[p] (PL M H) (PL M H)).liftBaseChange ℤ_[p]
  have hκ : LinearMap.ker κ = ⊥ :=
    LinearMap.ker_eq_bot.mpr (liftBaseChange_baseChangeHom_injective (A := ℤ_[p]) b)
  have h3 := h2.map' κ hκ
  convert h3 using 1 <;> try rfl
  funext k
  simp only [Function.comp_apply, κ, LinearMap.liftBaseChange_tmul, LinearMap.baseChangeHom_apply,
    one_smul, PendL_apply]

theorem exists_eq_natCast_mul_of_baseChange_eq (t : TT M H) {m : ℕ} (c : Fin m → ℤ_[p])
    (σ : Fin m → TT M H)
    (ht : (Pend M H t).baseChange ℤ_[p] = ∑ i, ((p : ℤ_[p]) * c i) • (Pend M H (σ i)).baseChange ℤ_[p]) :
    ∃ t' : TT M H, t = (p : TT M H) * t' := by
  classical

  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup
      (Gam M H) (isCong M H)
  haveI : Module.Free ℤ (PL M H) := Module.Free.of_basis b
  haveI : Module.Finite ℤ (PL M H) := Module.Finite.of_basis b
  haveI : Module.Finite ℤ (TT M H) := Module.Finite.of_injective (PendL M H) (PendL_injective M H)
  haveI : Module.IsTorsionFree ℤ (TT M H) :=
    (PendL_injective M H).moduleIsTorsionFree (PendL M H) (fun r x => map_zsmul _ r x)
  haveI : Module.Free ℤ (TT M H) := Module.free_of_finite_type_torsion_free'
  obtain ⟨τ⟩ : Nonempty (Module.Basis (Module.Free.ChooseBasisIndex ℤ (TT M H)) ℤ (TT M H)) :=
    ⟨Module.Free.chooseBasis ℤ (TT M H)⟩

  have hind := linearIndependent_baseChange_Pend M H p τ

  let BL : TT M H →ₗ[ℤ] (ℤ_[p] ⊗[ℤ] PL M H →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] PL M H) :=
    (LinearMap.baseChangeHom ℤ ℤ_[p] (PL M H) (PL M H)) ∘ₗ PendL M H
  have hBL : ∀ u, BL u = (Pend M H u).baseChange ℤ_[p] := fun u => rfl
  have expand : ∀ u : TT M H,
      (Pend M H u).baseChange ℤ_[p] =
        ∑ k, ((τ.repr u k : ℤ) : ℤ_[p]) • (Pend M H (τ k)).baseChange ℤ_[p] := fun u => by
    rw [← hBL]
    conv_lhs => rw [← τ.sum_repr u]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_zsmul, hBL, Int.cast_smul_eq_zsmul]
  set β : Module.Free.ChooseBasisIndex ℤ (TT M H) → ℤ_[p] :=
    fun k => ∑ i, (p : ℤ_[p]) * c i * ((τ.repr (σ i) k : ℤ) : ℤ_[p]) with hβdef
  clear_value β
  have hβ : (Pend M H t).baseChange ℤ_[p] = ∑ k, β k • (Pend M H (τ k)).baseChange ℤ_[p] := by
    rw [ht]
    have : ∀ i, ((p : ℤ_[p]) * c i) • (Pend M H (σ i)).baseChange ℤ_[p] =
        ∑ k, ((p : ℤ_[p]) * c i * ((τ.repr (σ i) k : ℤ) : ℤ_[p])) •
          (Pend M H (τ k)).baseChange ℤ_[p] := by
      intro i
      rw [expand (σ i), Finset.smul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [smul_smul]
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_smul]
    simp only [hβdef]
  have hcoef : ∀ k, ((τ.repr t k : ℤ) : ℤ_[p]) = β k := by
    have h0 : ∑ k, (((τ.repr t k : ℤ) : ℤ_[p]) - β k) • (Pend M H (τ k)).baseChange ℤ_[p] = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, ← expand t, ← hβ, sub_self]
    have := Fintype.linearIndependent_iff.mp hind _ h0
    intro k
    exact sub_eq_zero.mp (this k)

  have hdvd : ∀ k, (p : ℤ) ∣ τ.repr t k := fun k => by
    have h1 : (p : ℤ_[p]) ∣ ((τ.repr t k : ℤ) : ℤ_[p]) := by
      rw [hcoef, hβdef]
      exact Finset.dvd_sum (fun i _ => Dvd.intro (c i * ((τ.repr (σ i) k : ℤ) : ℤ_[p])) (by ring))
    exact (PadicInt.norm_int_lt_one_iff_dvd _).mp ((PadicInt.norm_lt_one_iff_dvd _).mpr h1)

  refine ⟨∑ k, (τ.repr t k / p) • τ k, ?_⟩
  rw [Finset.mul_sum]
  conv_lhs => rw [← τ.sum_repr t]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc]
  congr 1
  have : ((p : ℤ) : TT M H) = (p : TT M H) := Int.cast_natCast p
  rw [← this, ← Int.cast_mul, Int.mul_ediv_cancel' (hdvd k)]

variable (e : TateModule p (ModularCurve.JH M H) ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] PL M H)

abbrev conjE : Module.End ℤ_[p] (ℤ_[p] ⊗[ℤ] PL M H) ≃ₐ[ℤ_[p]]
    Module.End ℤ_[p] (TateModule p (ModularCurve.JH M H)) :=
  e.symm.conjAlgEquiv ℤ_[p]

def phi : TT M H →+* Module.End ℤ_[p] (TateModule p (ModularCurve.JH M H)) :=
  ((conjE M H p e).toAlgHom.toRingHom.comp
    (Module.End.baseChangeHom ℤ ℤ_[p] (PL M H)).toRingHom).comp (PendRing M H)

theorem phi_apply' (t : TT M H) :
    phi M H p e t = conjE M H p e ((Pend M H t).baseChange ℤ_[p]) := rfl

theorem phi_apply (t : TT M H) (x : TateModule p (ModularCurve.JH M H)) :
    phi M H p e t x = e.symm (((Pend M H t).baseChange ℤ_[p]) (e x)) := rfl

def IsComparison : Prop :=
  ∀ (g : CohCarrier.Gen M (∅ : Set ℕ)) (ψ : CohCarrier.H1 M H ℤ_[p]),
    ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] →
    ∀ (χ χ' : ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →ₗ[ℤ] ℤ_[p]),
      (∀ δ : CohCarrier.GammaH M H,
        χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
          ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
          ψ (Additive.ofMul δ)) →
      (∀ δ : CohCarrier.GammaH M H,
        χ' ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
          ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
          CohCarrier.opFamily M H ∅ ℤ_[p] g ψ (Additive.ofMul δ)) →
      ∀ x : TateModule p (ModularCurve.JH M H),
        χ'.liftBaseChange ℤ_[p] (e x) =
          χ.liftBaseChange ℤ_[p] (e (ModularCurve.tateGenOpH M H ∅ p g x))

theorem baseChange_Pend_gen_apply {e} (he : IsComparison M H p e) (g : CohCarrier.Gen M (∅ : Set ℕ))
    (x : TateModule p (ModularCurve.JH M H)) :
    ((Pend M H ⟨CuspForm.heckeGenH (H := H) ∅ 2 g, CuspForm.heckeGenH_mem_heckeRingH ∅ 2 g⟩).baseChange
        ℤ_[p]) (e x) = e (ModularCurve.tateGenOpH M H ∅ p g x) := by
  apply sep M H p
  intro χ
  set t : TT M H := ⟨CuspForm.heckeGenH (H := H) ∅ 2 g, CuspForm.heckeGenH_mem_heckeRingH ∅ 2 g⟩
  let ψ : CohCarrier.H1 M H ℤ_[p] := χ.toAddMonoidHom.comp (perHom M H)
  have hpar : ψ ∈ ModularCurve.Period.parabolicHoms ℤ_[p] (CohCarrier.GammaH M H) ℤ_[p] := by
    intro γ hγ
    have h0 : perHom M H (Additive.ofMul γ) = 0 := Subtype.ext (periodOf_eq_zero_of_trace M H γ hγ)
    simp only [ψ, AddMonoidHom.comp_apply, h0, map_zero]
  have h1 : ∀ δ : CohCarrier.GammaH M H,
      χ ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
        ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
        ψ (Additive.ofMul δ) := fun δ => rfl
  have h2 : ∀ δ : CohCarrier.GammaH M H,
      (χ ∘ₗ Pend M H t) ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
        ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
        CohCarrier.opFamily M H ∅ ℤ_[p] g ψ (Additive.ofMul δ) := fun δ => by
    obtain ⟨γ₀, hop, hper⟩ := exists_gen_universal M H g δ
    rw [hop ℤ_[p] ψ, LinearMap.comp_apply]
    have : Pend M H t ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) δ,
        ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) δ⟩ =
        ⟨ModularCurve.periodOf (CohCarrier.GammaH M H) γ₀,
          ModularCurve.periodOf_mem_periodLatticeOf (CohCarrier.GammaH M H) γ₀⟩ :=
      Subtype.ext (dualMap_gen_periodOf M H g δ γ₀ hper)
    rw [this]
    rfl
  have key := he g ψ hpar χ (χ ∘ₗ Pend M H t) h1 h2 x
  rw [← key]
  generalize e x = w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]

theorem phi_gen {e} (he : IsComparison M H p e) (g : CohCarrier.Gen M (∅ : Set ℕ)) :
    phi M H p e ⟨CuspForm.heckeGenH (H := H) ∅ 2 g, CuspForm.heckeGenH_mem_heckeRingH ∅ 2 g⟩ =
      ModularCurve.tateGenOpH M H ∅ p g := by
  apply LinearMap.ext
  intro x
  rw [phi_apply, LinearEquiv.symm_apply_eq]
  exact baseChange_Pend_gen_apply M H p he g x

theorem conjE_symm_phi (u : TT M H) :
    (conjE M H p e).toLinearEquiv.symm (phi M H p e u) = (Pend M H u).baseChange ℤ_[p] := by
  rw [phi_apply']
  exact (conjE M H p e).toLinearEquiv.symm_apply_apply _

theorem baseChange_mem_of_mem (t : TT M H)
    (ht : phi M H p e t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range (phi M H p e))) :
    (Pend M H t).baseChange ℤ_[p] ∈ Ideal.span {(p : ℤ_[p])} •
      Submodule.span ℤ_[p] (Set.range (fun u : TT M H => (Pend M H u).baseChange ℤ_[p])) := by
  set θ := (conjE M H p e).toLinearEquiv.symm with hθdef
  have hθ : ∀ u, θ (phi M H p e u) = (Pend M H u).baseChange ℤ_[p] := conjE_symm_phi M H p e
  have h1 : θ (phi M H p e t) ∈
      (Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range (phi M H p e))).map
        θ.toLinearMap :=
    Submodule.mem_map_of_mem ht
  rw [Submodule.map_smul'', Submodule.map_span, hθ] at h1
  have hrange : (θ.toLinearMap : _ → _) '' Set.range (phi M H p e) =
      Set.range (fun u : TT M H => (Pend M H u).baseChange ℤ_[p]) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hθ)
  rw [hrange] at h1
  exact h1

theorem exists_sum_of_mem_smul_span {S B : Type*} [CommRing S] [AddCommGroup B] [Module S B]
    {ι : Type*} (v : ι → B) (a : S) {x : B}
    (hx : x ∈ Ideal.span {a} • Submodule.span S (Set.range v)) :
    ∃ (m : ℕ) (c : Fin m → S) (σ : Fin m → ι), x = ∑ i, (a * c i) • v (σ i) := by
  classical
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨y, hy, hpy⟩ := hx
  obtain ⟨m, c, s, hsum⟩ := Submodule.mem_span_set'.mp hy
  have hs : ∀ i, ∃ u : ι, v u = s i := fun i => (s i).2
  choose σ hσ using hs
  refine ⟨m, c, σ, ?_⟩
  rw [← hpy, ← hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul, hσ]

theorem exists_baseChange_eq_of_mem (t : TT M H)
    (ht : phi M H p e t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range (phi M H p e))) :
    ∃ (m : ℕ) (c : Fin m → ℤ_[p]) (σ : Fin m → TT M H),
      (Pend M H t).baseChange ℤ_[p] =
        ∑ i, ((p : ℤ_[p]) * c i) • (Pend M H (σ i)).baseChange ℤ_[p] :=
  exists_sum_of_mem_smul_span _ _ (baseChange_mem_of_mem M H p e t ht)

theorem faithful (t : TT M H)
    (ht : phi M H p e t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range (phi M H p e))) :
    ∃ t' : TT M H, t = (p : TT M H) * t' := by
  obtain ⟨m, c, σ, h⟩ := exists_baseChange_eq_of_mem M H p e t ht
  exact exists_eq_natCast_mul_of_baseChange_eq M H p t c σ h

theorem galois_comm_gen (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (g : CohCarrier.Gen M (∅ : Set ℕ)) :
    ModularCurve.JH.tateGaloisRep M H p σ * ModularCurve.tateGenOpH M H ∅ p g =
      ModularCurve.tateGenOpH M H ∅ p g * ModularCurve.JH.tateGaloisRep M H p σ := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact ModularCurve.galois_smul_genOpH_comm M H ∅ σ g _

theorem galois_comm {e} (he : IsComparison M H p e) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (t : TT M H) :
    ModularCurve.JH.tateGaloisRep M H p σ * phi M H p e t =
      phi M H p e t * ModularCurve.JH.tateGaloisRep M H p σ :=
  commute_map_of_gen M H (phi M H p e) _ (fun g => by
    rw [phi_gen M H p he g]
    exact galois_comm_gen M H p σ g) t

theorem continuity (d : ℕ) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ a : TateModule p (ModularCurve.JH M H), ModularCurve.JH.tateGaloisRep M H p σ a - a ∈
          Ideal.span {(p : ℤ_[p])} ^ d • (⊤ : Submodule ℤ_[p] (TateModule p (ModularCurve.JH M H))) := by
  obtain ⟨L, hL, hfix⟩ := ModularCurve.JH.exists_finiteDimensional_smul_eq_self_of_torsion M H
    (p ^ d) (pow_pos (Fact.out : p.Prime).pos d)
  refine ⟨L, hL, fun σ hσ a => ?_⟩
  rw [← PadicInt.maximalIdeal_eq_span_p]
  exact TateModule.rep_sub_mem_of_forall_torsionBy σ d
    (fun m hm => hfix σ hσ m ((Submodule.mem_torsionBy_iff _ _).mp hm)) a

theorem eichlerShimura {e} (he : IsComparison M H p e) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (hℓp : ℓ ≠ p) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ ℓ) :
    phi M H p e ⟨CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2
          (CohCarrier.Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM),
        CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) 2
          (CohCarrier.Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM)⟩ *
        ModularCurve.JH.tateGaloisRep M H p σ =
      phi M H p e ⟨CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2
          (CohCarrier.Gen.dia
            (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))),
        CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) 2
          (CohCarrier.Gen.dia
            (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))⟩ *
        (ModularCurve.JH.tateGaloisRep M H p σ * ModularCurve.JH.tateGaloisRep M H p σ) +
      (ℓ : ℤ_[p]) • (1 : Module.End ℤ_[p] (TateModule p (ModularCurve.JH M H))) := by
  rw [phi_gen M H p he, phi_gen M H p he]
  exact mul_eq_of_quadratic _ _ _ ℓ (fun x =>
    ModularCurve.frobeniusQuadratic_tateModule_jH M p H ∅ (ModularCurve.heckeDiamondInputsHAll M H)
      hℓ (Set.notMem_empty ℓ) hℓM hℓp P hP σ hσ x)

theorem main :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ_[p] A) (_ : Module.Finite ℤ_[p] A)
      (_ : Module.Free ℤ_[p] A)
      (φ : CuspForm.heckeRingH M H 2 →+* Module.End ℤ_[p] A)
      (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] A),
      (∀ t : CuspForm.heckeRingH M H 2,
          φ t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range φ) →
            ∃ t' : CuspForm.heckeRingH M H 2, t = (p : CuspForm.heckeRingH M H 2) * t') ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : CuspForm.heckeRingH M H 2),
          ρ σ * φ t = φ t * ρ σ) ∧
      (∀ d : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
            ∀ a : A, ρ σ a - a ∈ Ideal.span {(p : ℤ_[p])} ^ d • (⊤ : Submodule ℤ_[p] A)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
          ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
              φ ⟨CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2
                    (CohCarrier.Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM),
                  CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) 2
                    (CohCarrier.Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM)⟩ * ρ σ =
                φ ⟨CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2
                    (CohCarrier.Gen.dia
                      (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))),
                  CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) 2
                    (CohCarrier.Gen.dia
                      (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))⟩ *
                  (ρ σ * ρ σ) +
                (ℓ : ℤ_[p]) • (1 : Module.End ℤ_[p] A)) := by
  obtain ⟨e, he⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf
      M p H ∅ (ModularCurve.heckeDiamondInputsHAll M H)
  have hfin := ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH M p H
  exact ⟨TateModule p (ModularCurve.JH M H), inferInstance, inferInstance, hfin.1, hfin.2,
    phi M H p e, ModularCurve.JH.tateGaloisRep M H p, faithful M H p e,
    fun σ t => galois_comm M H p he σ t, continuity M H p,
    fun ℓ hℓ hℓM hℓp P hP σ hσ => eichlerShimura M H p he ℓ hℓ hℓM hℓp P hP σ hσ⟩

end GalTwoAssembly
p2m_reactivate "P2MW.S_CuspForm_exists_padicGaloisModule_heckeRingH_two_frobenius_relation.GalTwoAssembly"

end
p2m_reactivate "P2MW.S_CuspForm_exists_padicGaloisModule_heckeRingH_two_frobenius_relation.GalTwoAssembly"

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime] :
    ∃ (A : Type) (_ : AddCommGroup A) (_ : Module ℤ_[p] A) (_ : Module.Finite ℤ_[p] A)
      (_ : Module.Free ℤ_[p] A)
      (φ : CuspForm.heckeRingH M H 2 →+* Module.End ℤ_[p] A)
      (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End ℤ_[p] A),
      (∀ t : CuspForm.heckeRingH M H 2,
          φ t ∈ Ideal.span {(p : ℤ_[p])} • Submodule.span ℤ_[p] (Set.range φ) →
            ∃ t' : CuspForm.heckeRingH M H 2, t = (p : CuspForm.heckeRingH M H 2) * t') ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : CuspForm.heckeRingH M H 2),
          ρ σ * φ t = φ t * ρ σ) ∧
      (∀ d : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
            ∀ a : A, ρ σ a - a ∈ Ideal.span {(p : ℤ_[p])} ^ d • (⊤ : Submodule ℤ_[p] A)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
          ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
              φ ⟨CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2
                    (CohCarrier.Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM),
                  CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) 2
                    (CohCarrier.Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM)⟩ * ρ σ =
                φ ⟨CuspForm.heckeGenH (H := H) (∅ : Set ℕ) 2
                    (CohCarrier.Gen.dia
                      (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))),
                  CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) 2
                    (CohCarrier.Gen.dia
                      (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))⟩ *
                  (ρ σ * ρ σ) +
                (ℓ : ℤ_[p]) • (1 : Module.End ℤ_[p] A)) :=
  GalTwoAssembly.main M H p

end S_CuspForm_exists_padicGaloisModule_heckeRingH_two_frobenius_relation
end P2MW
export P2MW.S_CuspForm_exists_padicGaloisModule_heckeRingH_two_frobenius_relation (solution)

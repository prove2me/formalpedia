-- Prove2me | solution 1 for CuspForm.mem_twoCompRegularDifferentials_of_diffQExp_eq_intSeriesC_of_diffQExp_eq_intSeriesC_alSlash
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/10fc151d-13f5-5a5f-87aa-83e39aa0507e

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff
import Theorems.Thm_CuspForm_add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC
import Theorems.Thm_ModularCurve_diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
import Theorems.Thm_AlgebraicCurve_Place_isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_smul_pullbackAlong_of_algEquiv
import Theorems.Thm_ModularCurve_diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash
import Theorems.Thm_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
import Theorems.Thm_ModularCurve_exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_kaehlerD_ne_zero_of_ord_eq_one
import Theorems.Thm_CuspForm_exists_isIntegralQExp_and_alSlash_of_mem_twoCuspIntegralSet
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_mem_twoCompRegularDifferentials_of_diffQExp_eq_intSeriesC_of_diffQExp_eq_intSeriesC_alSlash
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero"
p2m_attr_erase "instance" "ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst"
p2m_attr_erase "simp" "ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem resopp_aux_add_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) (hd : v.dCoord ≠ 0) {η η' : Ω[F⁄K]} {a b : K}
    (ha : v.HasSimpleResidue η a) (hb : v.HasSimpleResidue η' b) (hreg : v.IsRegularAt (η + η')) :
    a + b = 0 := by
  obtain ⟨f, rfl, hfa⟩ := ha
  obtain ⟨g, rfl, hgb⟩ := hb
  obtain ⟨h, hh, hsum⟩ := hreg
  have hfg : f + g = h := by
    have h0 : (f + g - h) • v.dCoord = 0 := by rw [sub_smul, add_smul, hsum, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hd)

  have hval : v.HasValue (v.uniformizer * (f + g)) (a + b) := by
    refine ⟨by rw [mul_add]; exact add_mem hfa.mem hgb.mem, ?_⟩
    have e1 : (⟨v.uniformizer * (f + g), by rw [mul_add]; exact add_mem hfa.mem hgb.mem⟩ : v.toValuationSubring) =
        ⟨v.uniformizer * f, hfa.mem⟩ + ⟨v.uniformizer * g, hgb.mem⟩ := Subtype.ext (mul_add _ _ _)
    rw [e1, map_add, hfa.residue_eq, hgb.residue_eq, ← map_add]

  have hval0 : v.HasValue (v.uniformizer * (f + g)) 0 := by
    obtain ⟨h', hh', hv0⟩ := AlgebraicCurve.Place.hasSimpleResidue_zero_of_mem hh
    have : h' = h := ((smul_eq_zero.mp (by rw [sub_smul, ← hh', sub_self] : (h' - h) • v.dCoord = 0)).resolve_right hd) |> sub_eq_zero.mp
    rw [hfg, ← this]; exact hv0
  exact hval.unique hval0

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (W : ModularForm.AtkinLehnerDatum M p)
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf pfW : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf)
    (hpfW : ModularCurve.IsIntegralQExp (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 e f)) pfW)
    (ω ω' : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hω : ω ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)
    (hω' : ω' ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)
    (hΘ : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω = ModularCurve.intSeriesC K pf)
    (hΘ' : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω' = ModularCurve.intSeriesC K pfW) :
    (ω, ω') ∈ ModularCurve.twoCompRegularDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by
  classical

  haveI hN0 : NeZero (M / p) := ModularCurve.neZero_div p M hpM
  have hpN : ¬ p ∣ M / p := fun h => hpM2 (by rw [pow_two, ← Nat.mul_div_cancel' hpM]; exact Nat.mul_dvd_mul_left p h)
  have hT := ModularCurve.translation_mem_GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)
  obtain ⟨x, -, htr, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K
    (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
  haveI := hfd
  set ebar : (ZMod (M / p))ˣ := ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e with hebar

  have hbij := ModularCurve.qExpFrobeniusPlaceModL_bijective K p (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
  have himg := ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq K p (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))

  obtain ⟨hdss, hfrob2⟩ := ModularCurve.diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
    K p (M / p) hpN (ModularCurve.infSubgroup p M H hpM)
  obtain ⟨-, -, -, -, -, -, hinv⟩ := ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul K (M / p)
    (ModularCurve.infSubgroup p M H hpM)
  have htrans := fun w η => AlgebraicCurve.Place.isRegularAt_and_hasSimplePoleAt_and_hasSimpleResidue_smul_pullbackAlong_of_algEquiv
    htr hfd (ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) ebar⁻¹)) w η

  apply AlgebraicCurve.mem_gluedPolarDifferentials_of_isGluedPolarPair
  have hfst : Prod.fst '' ModularCurve.ssNodePairsQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p =
      ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by
    rw [← himg]
    ext w
    constructor
    · rintro ⟨⟨w₁, w₂⟩, ⟨h₂, h₁⟩, rfl⟩
      exact ⟨w₂, h₂, h₁.symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p y, y), ⟨hy, rfl⟩, rfl⟩
  have hsnd : Prod.snd '' ModularCurve.ssNodePairsQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p =
      ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by
    ext w
    constructor
    · rintro ⟨⟨w₁, w₂⟩, ⟨h₂, -⟩, rfl⟩
      exact h₂
    · intro hw
      exact ⟨(ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p w, w), ⟨hw, rfl⟩, rfl⟩
  refine ⟨by rw [hfst]; exact hω, by rw [hsnd]; exact hω', ?_⟩
  rintro ⟨y₁, y⟩ ⟨hy, hy₁⟩ a b ha hb
  dsimp only at hy hy₁ ha hb
  subst hy₁

  set f₁ : CuspForm (CohCarrier.GammaH M H) 2 := CuspForm.diamondLinH 2 e f with hf₁def
  have hf₁ : f₁ ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
    have := CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (CuspForm.heckeGenH_mem_heckeRingH (M := M) (H := H) (∅ : Set ℕ) 2 (.dia e)) hf
    simpa using this
  obtain ⟨⟨pef, hpef⟩, -⟩ := CuspForm.exists_isIntegralQExp_and_alSlash_of_mem_twoCuspIntegralSet p M H W e f₁ hf₁
  have hHp' : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := by
    have key : ∀ (n₁ n₂ : ℕ) (hn : n₁ = n₂) (h₁ : n₁ ∣ M) (h₂ : n₂ ∣ M) (u : (ZMod M)ˣ),
        ZMod.unitsMap h₁ u = 1 → ZMod.unitsMap h₂ u = 1 := by
      intro n₁ n₂ hn; subst hn; intro h₁ h₂ u h; exact h
    have hR : M / p = W.R := Nat.div_eq_of_eq_mul_left (Fact.out : p.Prime).pos (W.hM.trans (mul_comm _ _))
    exact fun u hu => hHp u (key _ _ hR.symm _ _ u hu)
  obtain ⟨h₁, hh₁⟩ := CuspForm.exists_GammaH_coe_eq_alSlash (Fact.out : p.Prime) W H hHp' 2 (CuspForm.diamondLinH 2 e f₁)
  obtain ⟨d', hd'1, -, hd'3⟩ := CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash M p hpM H hHp W 2 e⁻¹
    (CuspForm.diamondLinH 2 e f₁) h₁ hh₁
  have hd' : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d' : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)) := by
    rw [hd'1, map_inv]
    exact Units.inv_eq_of_mul_eq_one_right he
  have hD := CuspForm.stableD M H 2
  have hcoe : ⇑(CuspForm.diamondLinH 2 e⁻¹ (CuspForm.diamondLinH 2 e f₁)) = ⇑f₁ := by
    rw [CuspForm.coe_diamondLinH_apply 2 hD, CuspForm.coe_diamondLinH_apply 2 hD, ← SlashAction.slash_mul, ← map_mul]
    have key := CuspForm.slash_mapGL_eq_of_gamma0Units_eq (H := H) 2
      (fun γ hγ => SlashInvariantFormClass.slash_action_eq f₁ γ hγ) (CuspForm.gammaLift M e * CuspForm.gammaLift M e⁻¹) 1
      (by rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift, mul_inv_cancel, map_one]) 1
    rw [mul_one, mul_one] at key
    rw [show ((CuspForm.gammaLift M e : SL(2, ℤ)) * (CuspForm.gammaLift M e⁻¹ : SL(2, ℤ))) =
        ((CuspForm.gammaLift M e * CuspForm.gammaLift M e⁻¹ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) from rfl, key]
    rw [show ((1 : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) = 1 from rfl, map_one]
    exact SlashAction.slash_one 2 _
  have hpdh : ModularCurve.IsIntegralQExp ⇑(CuspForm.diamondLinH 2 d' h₁) pfW := by
    rw [← hd'3, hcoe]
    exact hpfW

  obtain ⟨C, hC⟩ := ModularCurve.exists_isFrobPushDiff_qExpFunctionFieldC_gammaH p K (M / p) (ModularCurve.infSubgroup p M H hpM)
  set ω₁ := ModularCurve.diamondDiffModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ebar ω with hω₁def
  have hΘ₁ : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω₁ =
      ModularCurve.intSeriesC K pef :=
    ModularCurve.diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet p M hpM hpM2 H hHp K f hf pf hpf e pef hpef ω hΘ
  have hreg := CuspForm.add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC p M hpM hpM2 H hHp K W e he C hC
    f₁ hf₁ h₁ hh₁ d' hd' pef pfW hpef hpdh ω₁ ω' hΘ₁ hΘ'

  have hω₁ : ω₁ ∈ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by
    rw [ModularCurve.mem_ssPolarDifferentials_iff] at hω ⊢
    intro w
    set u := AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) ebar)) • w with hu
    have hwu : AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) ebar⁻¹)) • u = w := (hinv _ w ebar).2
    have huss := hdss ebar w
    obtain ⟨hr, hp, -⟩ := htrans u ω
    rw [hwu] at hr hp
    exact ⟨fun hw => hr ((hω u).1 fun h => hw (huss.1 h)), fun hw => hp ((hω u).2 (huss.2 hw))⟩

  obtain ⟨v, rfl⟩ := hbij.2 y
  have hv : v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := by
    rw [← himg] at hy
    obtain ⟨v', hv', he'⟩ := hy
    rwa [← hbij.1 he']
  have hFF := hfrob2 ebar he v hv

  have ha₁ : v.HasSimpleResidue ω₁ a := by
    have h := (htrans _ ω).2.2 a (hFF ▸ ha)
    rwa [(hinv _ v ebar).2] at h

  have hCa := (ModularCurve.hasSimpleResidue_qExpFrobeniusPlaceModL_of_isFrobPushDiff K p
    (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT C hC ω₁ hω₁).2 v hv a ha₁

  have hord : (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v).ord (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v).uniformizer = 1 :=
    AlgebraicCurve.Place.ord_coe_irreducible (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v) (AlgebraicCurve.Place.irreducible_mk_uniformizer (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v))
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({x} : Set ↥(ModularCurve.qExpFunctionFieldC K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))))
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :=
    Algebra.IsAlgebraic.of_finite _ _
  have hdC : (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v).dCoord ≠ 0 := by
    rw [AlgebraicCurve.Place.dCoord_eq]
    exact AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one x (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v) hord
  have hreg' : (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v).IsRegularAt (C ω₁ + ω') := AlgebraicCurve.mem_regularDifferentials_iff.mp hreg (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v)
  exact resopp_aux_add_eq_zero (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v) hdC hCa hb hreg'

end S_CuspForm_mem_twoCompRegularDifferentials_of_diffQExp_eq_intSeriesC_of_diffQExp_eq_intSeriesC_alSlash
end P2MW
export P2MW.S_CuspForm_mem_twoCompRegularDifferentials_of_diffQExp_eq_intSeriesC_of_diffQExp_eq_intSeriesC_alSlash (solution)

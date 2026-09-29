-- Prove2me | solution 1 for CuspForm.forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a8097010-c22f-5534-86f2-e387d66ce2f6

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range
import Theorems.Thm_ModularCurve_intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ"
p2m_attr_erase "simp" "ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open scoped MatrixGroups ModularForm
open ModularFormClass

namespace DiaInt

theorem exists_int_of_pow_mul_eq_int (p : ℕ) [Fact p.Prime] (r : ℚ) (hr : r ∈ GaloisRep.ratLocalizedAt p)
    (v : ℕ) (m : ℤ) (h : (p : ℚ) ^ v * r = m) : ∃ n : ℤ, (n : ℚ) = r := by
  have hcop : r.den.Coprime p := hr

  have key : (p : ℤ) ^ v * r.num = m * r.den := by
    have h1 := Rat.num_div_den r
    have hden0 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
    have : ((p : ℚ) ^ v * r.num) = (m : ℚ) * r.den := by
      rw [← h, mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast this

  have hdvd : (r.den : ℤ) ∣ (p : ℤ) ^ v * r.num := ⟨m, by rw [key, mul_comm]⟩
  have hdvd' : (r.den : ℤ) ∣ (p : ℤ) ^ v := by
    have hc : IsCoprime (r.den : ℤ) r.num := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      exact_mod_cast r.reduced
    exact hc.dvd_of_dvd_mul_right hdvd
  have hdvdN : r.den ∣ p ^ v := by exact_mod_cast (Int.natCast_dvd_natCast.mp (by exact_mod_cast hdvd'))
  have hone : r.den = 1 := Nat.Coprime.eq_one_of_dvd (hcop.pow_right v) hdvdN
  exact ⟨r.num, by have := Rat.num_div_den r; rw [hone, Nat.cast_one, div_one] at this; exact this⟩

section Forms

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}

abbrev GH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  (CohCarrier.GammaH M H : Subgroup SL(2, ℤ)).map (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem gamma1GL_le_GH : (CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)).map (Matrix.SpecialLinearGroup.mapGL ℝ) ≤ GH M H :=
  Subgroup.map_mono (ModularCurve.Gamma1_le_GammaH M H)

theorem one_mem_strictPeriods_GH : (1 : ℝ) ∈ (GH M H).strictPeriods := by
  have h := CongruenceSubgroup.strictPeriods_Gamma1 M
  have h1 : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)).map (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [h]; exact AddSubgroup.mem_zmultiples 1
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  exact gamma1GL_le_GH h1

def toMF (F : CuspForm (GH M H) k) : ModularForm (GH M H) k where
  toSlashInvariantForm := F.toSlashInvariantForm
  holo' := F.holo'
  bdd_at_cusps' hc := fun g hg => (F.zero_at_cusps' hc g hg).boundedAtFilter

@[scoped simp] theorem coe_toMF (F : CuspForm (GH M H) k) : (⇑(toMF F) : UpperHalfPlane → ℂ) = ⇑F := rfl

theorem qExpansion_smul_cuspForm (c : ℂ) (F : CuspForm (GH M H) k) :
    UpperHalfPlane.qExpansion 1 (c • (⇑F : UpperHalfPlane → ℂ)) = c • UpperHalfPlane.qExpansion 1 ⇑F :=
  ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_GH c F

theorem qCoeff_smul_cuspForm (c : ℂ) (F : CuspForm (GH M H) k) (n : ℕ) :
    qCoeff (c • (⇑F : UpperHalfPlane → ℂ)) n = c * qCoeff ⇑F n := by
  simp only [qCoeff, qExpansion_smul_cuspForm, map_smul, smul_eq_mul]

end Forms

open CongruenceSubgroup in
theorem main
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (k : ℤ) (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k)
    (hf : ∀ n : ℕ, qCoeff (⇑f) n ∈ ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ))) :
    ∀ n : ℕ, qCoeff (⇑(CuspForm.diamondLinH k d f)) n ∈ ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)) := by
  classical
  have hp : p.Prime := Fact.out
  have hD := CuspForm.stableD M H k

  obtain ⟨R, hMR⟩ := hpM
  have hpR : ¬ p ∣ R := fun h => hpM2 (by rw [hMR, pow_two]; exact Nat.mul_dvd_mul_left p h)

  have hfQ : ∀ n : ℕ, qCoeff (⇑f) n ∈ (algebraMap ℚ ℂ).range := fun n => by
    obtain ⟨r, -, hr⟩ := Subring.mem_map.mp (hf n); exact ⟨r, hr⟩
  obtain ⟨D, hD0, hDint⟩ :=
    CuspForm.exists_ne_zero_forall_natCast_mul_qCoeff_mem_bot_of_forall_qCoeff_mem_range M H k f hfQ
  let v := padicValNat p D
  obtain ⟨D', hDD'⟩ : p ^ v ∣ D := pow_padicValNat_dvd
  have hD'0 : D' ≠ 0 := fun h => hD0 (by rw [hDD', h, mul_zero])
  have hpD' : ¬ p ∣ D' := by
    intro h
    have : p ^ (v + 1) ∣ D := by rw [hDD', pow_succ]; exact Nat.mul_dvd_mul_left _ h
    exact pow_succ_padicValNat_not_dvd hD0 this

  have hcoef : ∀ n : ℕ, ∃ m : ℤ, (m : ℂ) = (D' : ℂ) * qCoeff (⇑f) n := by
    intro n
    obtain ⟨r, hr, hrn⟩ := Subring.mem_map.mp (hf n)
    obtain ⟨m, hm⟩ := Subring.mem_bot.mp (hDint n)

    have hq : (p : ℚ) ^ v * ((D' : ℚ) * r) = m := by
      have e : ((m : ℤ) : ℂ) = (D : ℂ) * algebraMap ℚ ℂ r := by rw [hm, hrn]
      rw [hDD'] at e
      push_cast at e
      have e' : (algebraMap ℚ ℂ) ((p : ℚ) ^ v * ((D' : ℚ) * r)) = algebraMap ℚ ℂ (m : ℚ) := by
        simp only [map_mul, map_pow, map_natCast, eq_ratCast, Rat.cast_intCast]
        rw [e]; simp only [eq_ratCast]; ring
      exact (algebraMap ℚ ℂ).injective e'
    have hmem : (D' : ℚ) * r ∈ GaloisRep.ratLocalizedAt p := Subring.mul_mem _ (natCast_mem _ _) hr
    obtain ⟨m', hm'⟩ := exists_int_of_pow_mul_eq_int p _ hmem v m hq
    refine ⟨m', ?_⟩
    rw [← hrn, show (m' : ℂ) = algebraMap ℚ ℂ (m' : ℚ) by simp, hm', map_mul, map_natCast]
  choose c hc using hcoef
  let P : PowerSeries ℤ := PowerSeries.mk c
  let h : CuspForm (CohCarrier.GammaH M H) k := (D' : ℂ) • f
  have hcoeh : (⇑h : UpperHalfPlane → ℂ) = (D' : ℂ) • ⇑f := by rfl
  have hP : ModularCurve.IsIntegralQExp (⇑h) P := by
    rw [ModularCurve.isIntegralQExp_iff]
    intro n
    rw [PowerSeries.coeff_mk, hc n, hcoeh, ← qCoeff, qCoeff_smul_cuspForm]

  let γ : SL(2, ℤ) := ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ))
  have hγ : γ ∈ Gamma0 M := (CuspForm.gammaLift M d).2
  obtain ⟨a, f₁, p₁, hp₁, hf₁⟩ := ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 M
    (ModularCurve.restrictForm gamma1GL_le_GH (toMF h)) hP γ hγ
  rw [ModularCurve.coe_restrictForm, coe_toMF] at hf₁
  have hdh : (⇑(CuspForm.diamondLinH k d h) : UpperHalfPlane → ℂ) = (⇑h : UpperHalfPlane → ℂ) ∣[k] γ := by
    rw [CuspForm.coe_diamondLinH_apply k hD, ModularForm.SL_slash]; rfl
  have hM0 : ((M : ℂ) ^ a) ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne M)
  have hqd : UpperHalfPlane.qExpansion 1 ⇑(CuspForm.diamondLinH k d h) = ((M : ℂ) ^ a)⁻¹ • p₁.map (Int.castRingHom ℂ) := by
    rw [hp₁, hf₁, ← hdh, qExpansion_smul_cuspForm, smul_smul, inv_mul_cancel₀ hM0, one_smul]

  have hdiv : ∀ n, (p : ℤ) ^ a ∣ PowerSeries.coeff n p₁ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨n₀, hn₀⟩ := hcon
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · exact absurd (by rw [h0, pow_zero]; exact one_dvd _) hn₀
      · exact h0
    have hex : ∃ w, ∃ n, ¬ (p : ℤ) ^ (w + 1) ∣ PowerSeries.coeff n p₁ := ⟨a - 1, n₀, by rwa [Nat.sub_add_cancel ha]⟩
    obtain ⟨n₁, hn₁⟩ : ∃ n, ¬ (p : ℤ) ^ (Nat.find hex + 1) ∣ PowerSeries.coeff n p₁ := Nat.find_spec hex
    set w := Nat.find hex with hw
    have hwmin : ∀ n, (p : ℤ) ^ w ∣ PowerSeries.coeff n p₁ := by
      intro n
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0, pow_zero]; exact one_dvd _
      · have hmin := Nat.find_min hex (m := w - 1) (by omega)
        push_neg at hmin
        have := hmin n
        rwa [Nat.sub_add_cancel h0] at this
    have hwa : w < a := by
      have : Nat.find hex ≤ a - 1 := Nat.find_le ⟨n₀, by rwa [Nat.sub_add_cancel ha]⟩
      omega
    choose e he using hwmin
    let Q : PowerSeries ℤ := PowerSeries.mk e
    have hpQ : p₁ = PowerSeries.C ((p : ℤ) ^ w) * Q := by
      ext n; rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]; exact he n
    have hQ0 : ModularCurve.intSeriesC (ZMod p) Q ≠ 0 := by
      intro h0
      apply hn₁
      have hc0 : ((e n₁ : ℤ) : ZMod p) = 0 := by
        have := congrArg (fun s : LaurentSeries (ZMod p) => s.coeff (n₁ : ℤ)) h0
        simpa [ModularCurve.intSeriesC, Q] using this
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc0
      rw [he n₁, pow_succ]
      exact mul_dvd_mul_left _ hc0

    let N₃ : ℤ := (p : ℤ) ^ (a - w) * (R : ℤ) ^ a
    have hpw : ((p : ℂ) ^ w) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    have hcst : ((M : ℂ) ^ a) * ((p : ℂ) ^ w)⁻¹ = (N₃ : ℂ) := by
      rw [hMR]; push_cast
      rw [mul_pow, show (p : ℂ) ^ a = (p : ℂ) ^ (a - w) * (p : ℂ) ^ w by rw [← pow_add, Nat.sub_add_cancel hwa.le]]
      field_simp
      simp [N₃]
    let cst : ℂ := (N₃ : ℂ)
    let h₂ : ModularForm (GH M H) k := cst • toMF (CuspForm.diamondLinH k d h)
    let h₃ : ModularForm (GH M H) k := cst • toMF h
    have hQ : ModularCurve.IsIntegralQExp ⇑h₂ Q := by
      show Q.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑h₂
      have e1 : (⇑h₂ : UpperHalfPlane → ℂ) = cst • ⇑(CuspForm.diamondLinH k d h) := rfl
      rw [e1, qExpansion_smul_cuspForm, hqd, hpQ, map_mul, PowerSeries.map_C, ← PowerSeries.smul_eq_C_mul, smul_smul, smul_smul,
        show cst = ((M : ℂ) ^ a) * ((p : ℂ) ^ w)⁻¹ from hcst.symm]
      simp only [map_pow, map_natCast, eq_intCast, Int.cast_pow, Int.cast_natCast]
      rw [show (M : ℂ) ^ a * ((p : ℂ) ^ w)⁻¹ * ((M : ℂ) ^ a)⁻¹ * (p : ℂ) ^ w = 1 by field_simp, one_smul]
    have hP₃ : ModularCurve.IsIntegralQExp ⇑h₃ (PowerSeries.C N₃ * P) := by
      show (PowerSeries.C N₃ * P).map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑h₃
      have e1 : (⇑h₃ : UpperHalfPlane → ℂ) = cst • ⇑h := rfl
      rw [e1, qExpansion_smul_cuspForm, ← hP, map_mul, PowerSeries.map_C, ← PowerSeries.smul_eq_C_mul]
      simp only [eq_intCast]
      rfl
    have hP₃0 : ModularCurve.intSeriesC (ZMod p) (PowerSeries.C N₃ * P) = 0 := by
      have hN : ((N₃ : ℤ) : ZMod p) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
      have hmap : (PowerSeries.C N₃ * P).map (Int.castRingHom (ZMod p)) = 0 := by
        ext n
        rw [map_mul, PowerSeries.map_C, PowerSeries.coeff_C_mul, eq_intCast, hN, zero_mul, map_zero]
      simp only [ModularCurve.intSeriesC, hmap, map_zero]
    have hhs : (⇑h₃ : UpperHalfPlane → ℂ) = ((⇑h₂ : UpperHalfPlane → ℂ) ∣[k] γ⁻¹) := by
      show cst • (⇑h : UpperHalfPlane → ℂ) = (cst • (⇑(CuspForm.diamondLinH k d h) : UpperHalfPlane → ℂ)) ∣[k] γ⁻¹
      rw [hdh, ModularForm.SL_smul_slash, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    exact (ModularCurve.intSeriesC_ne_zero_of_coe_eq_slash_of_mem_Gamma0_of_level_mul p M ⟨R, hMR⟩ hpM2 H hHp (ZMod p)
      γ⁻¹ (inv_mem hγ) k h₂ h₃ Q (PowerSeries.C N₃ * P) hQ hP₃ hhs hQ0) hP₃0

  choose e' he' using hdiv
  have hdf : (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) = ((D' : ℂ))⁻¹ • ⇑(CuspForm.diamondLinH k d h) := by
    have : CuspForm.diamondLinH k d h = (D' : ℂ) • CuspForm.diamondLinH k d f := by
      show CuspForm.diamondLinH k d ((D' : ℂ) • f) = _; rw [map_smul]
    rw [this]
    ext z
    simp [hD'0]
  intro n
  have hD'C : (D' : ℂ) ≠ 0 := by exact_mod_cast hD'0
  have hcoefn : qCoeff (⇑(CuspForm.diamondLinH k d f)) n = ((D' : ℂ))⁻¹ * (((M : ℂ) ^ a)⁻¹ * ((p : ℂ) ^ a * (e' n : ℂ))) := by
    rw [hdf, qCoeff_smul_cuspForm, qCoeff, hqd]
    simp only [map_smul, PowerSeries.coeff_map, smul_eq_mul, eq_intCast, he' n, Int.cast_mul, Int.cast_pow, Int.cast_natCast]

  let r : ℚ := (e' n : ℚ) / ((D' : ℚ) * (R : ℚ) ^ a)
  have hrmem : r ∈ GaloisRep.ratLocalizedAt p := by
    have hinv : ∀ q : ℕ, q.Coprime p → ((q : ℚ))⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
      intro q hq
      show ((q : ℚ)⁻¹).den.Coprime p
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · subst h0; simpa using hq
      · rw [Rat.inv_natCast_den_of_pos h0]; exact hq
    have h1 : ((D' : ℚ))⁻¹ ∈ GaloisRep.ratLocalizedAt p := hinv D' ((Nat.coprime_comm).mp ((hp.coprime_iff_not_dvd).mpr hpD'))
    have h2 : ((R : ℚ) ^ a)⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
      rw [← Nat.cast_pow]; exact hinv _ (Nat.Coprime.pow_left a ((Nat.coprime_comm).mp ((hp.coprime_iff_not_dvd).mpr hpR)))
    have : r = (e' n : ℚ) * (((D' : ℚ))⁻¹ * ((R : ℚ) ^ a)⁻¹) := by
      simp only [r]; rw [div_eq_mul_inv, mul_inv]
    rw [this]
    exact Subring.mul_mem _ (intCast_mem _ _) (Subring.mul_mem _ h1 h2)
  refine Subring.mem_map.mpr ⟨r, hrmem, ?_⟩
  have hR0 : (R : ℂ) ≠ 0 := by
    have : R ≠ 0 := fun h0 => NeZero.ne M (by rw [hMR, h0, mul_zero])
    exact_mod_cast this
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hcoefn, hMR]
  simp only [r, map_div₀, map_mul, map_pow, map_natCast, eq_ratCast, Rat.cast_intCast, Nat.cast_mul, mul_pow]
  field_simp

end DiaInt
p2m_reactivate "P2MW.S_CuspForm_forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt.DiaInt"

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (k : ℤ) (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f) n ∈ ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ))) :
    ∀ n : ℕ, ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH k d f)) n ∈
      ((GaloisRep.ratLocalizedAt p).map (algebraMap ℚ ℂ)) :=
  DiaInt.main p M hpM hpM2 H hHp k d f hf

#print axioms solution

end S_CuspForm_forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt
end P2MW
export P2MW.S_CuspForm_forall_qCoeff_diamondLinH_mem_ratLocalizedAt_of_forall_qCoeff_mem_ratLocalizedAt (solution)

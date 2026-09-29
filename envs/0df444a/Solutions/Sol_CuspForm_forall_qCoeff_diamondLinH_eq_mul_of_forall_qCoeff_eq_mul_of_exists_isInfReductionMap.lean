-- Prove2me | solution 1 for CuspForm.forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2b0b657e-113a-5787-a16b-2514789fe7f0

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_LaurentSeries_injective_of_forall_apply_tmul_eq_smul_map
import Theorems.Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genDia_eq_genDiffModL_comp
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ"
p2m_attr_erase "simp" "ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped TensorProduct ModularForm MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "infSubgroup IsInfReductionMap Gamma1_le_GammaH IsIntegralQExp isIntegralQExp_iff IsIntegralQExp.unique isIntegralQExp_zero intSeriesC intSeriesC_zero qExpFunctionFieldC coeffMap coeffMap_coeff coeffMap_ofPowerSeries diffQExp IsInfReductionMap.comp_baseChange_genDia_eq_genDiffModL_comp diffQExp_qExpFunctionFieldC_injective"
namespace LinAuxD
p2m_open "ModularCurve"

def toZ (a : (⊥ : Subring ℂ)) : ℤ := (Subring.mem_bot.mp a.2).choose

theorem cast_toZ (a : (⊥ : Subring ℂ)) : ((toZ a : ℤ) : ℂ) = (a : ℂ) := (Subring.mem_bot.mp a.2).choose_spec

theorem toZ_add (a b : (⊥ : Subring ℂ)) : toZ (a + b) = toZ a + toZ b := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_add, cast_toZ, cast_toZ, cast_toZ, Subring.coe_add]

theorem toZ_mul (a b : (⊥ : Subring ℂ)) : toZ (a * b) = toZ a * toZ b := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_mul, cast_toZ, cast_toZ, cast_toZ, Subring.coe_mul]

theorem toZ_one : toZ 1 = 1 := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_one, Subring.coe_one]

theorem toZ_zero : toZ 0 = 0 := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_zero, Subring.coe_zero]

theorem toZ_natCast (n : ℕ) : toZ (n : (⊥ : Subring ℂ)) = n := by
  apply Int.cast_injective (α := ℂ)
  rw [cast_toZ, Int.cast_natCast]; rfl

def toZHom : (⊥ : Subring ℂ) →+* ℤ where
  toFun := toZ
  map_one' := toZ_one
  map_mul' := toZ_mul
  map_zero' := toZ_zero
  map_add' := toZ_add

theorem smul_eq_toZ_zsmul {V : Type*} [AddCommGroup V] [Module ℂ V] (a : (⊥ : Subring ℂ)) (v : V) :
    a • v = toZ a • v := by
  rw [Subring.smul_def, ← cast_toZ, Int.cast_smul_eq_zsmul]

theorem ofPowerSeries_coeff_neg {R : Type*} [CommRing R] (x : PowerSeries R) {n : ℤ} (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨m, hm⟩
  have hm' : (m : ℤ) = n := hm
  omega

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ofPowerSeries_coeff_neg _ hn, ofPowerSeries_coeff_neg _ hn, map_zero]
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

section Iota

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra (ZMod p) K]

def ιL : K ⊗[ZMod p] LaurentSeries (ZMod p) →ₗ[ZMod p] LaurentSeries K :=
  TensorProduct.lift
    (LinearMap.mk₂ (ZMod p) (fun (c : K) (f : LaurentSeries (ZMod p)) => c • coeffMap (algebraMap (ZMod p) K) f)
      (fun c d f => by rw [add_smul])
      (fun r c f => by rw [smul_assoc])
      (fun c f g => by rw [map_add, smul_add])
      (fun r c f => by
        ext n
        simp only [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul, Algebra.smul_def]
        ring))

theorem ιL_tmul (c : K) (f : LaurentSeries (ZMod p)) :
    ιL p K (c ⊗ₜ[ZMod p] f) = c • coeffMap (algebraMap (ZMod p) K) f :=
  TensorProduct.lift.tmul c f

theorem ιL_injective : Function.Injective (ιL p K) :=
  LaurentSeries.injective_of_forall_apply_tmul_eq_smul_map (ZMod p) K (ιL p K) (fun a f => ιL_tmul p K a f)

def ofPS : PowerSeries (ZMod p) →ₗ[ZMod p] LaurentSeries (ZMod p) where
  toFun := HahnSeries.ofPowerSeries ℤ (ZMod p)
  map_add' s t := map_add _ s t
  map_smul' r s := by
    rw [RingHom.id_apply, PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem ofPS_apply (s : PowerSeries (ZMod p)) : ofPS p s = HahnSeries.ofPowerSeries ℤ (ZMod p) s := rfl

theorem ofPS_injective : Function.Injective (ofPS p) := fun a b h => HahnSeries.ofPowerSeries_injective h

theorem ι_injective : Function.Injective (ιL p K ∘ₗ LinearMap.lTensor K (ofPS p)) := by
  rw [LinearMap.coe_comp]
  exact (ιL_injective p K).comp (Module.Flat.lTensor_preserves_injective_linearMap _ (ofPS_injective p))

theorem ι_tmul (c : K) (s : PowerSeries (ZMod p)) :
    (ιL p K ∘ₗ LinearMap.lTensor K (ofPS p)) (c ⊗ₜ[ZMod p] s) =
      c • HahnSeries.ofPowerSeries ℤ K (s.map (algebraMap (ZMod p) K)) := by
  rw [LinearMap.comp_apply, LinearMap.lTensor_tmul, ιL_tmul, ofPS_apply, coeffMap_ofPowerSeries]

end Iota

section Main

variable (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
  (K : Type*) [Field K] [Algebra (ZMod p) K]

local notation "Γ" => CohCarrier.GammaH M H
local notation "A" => (⊥ : Subring ℂ)
local notation "L" => CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)
local notation "Ω₀" => CuspForm.IntTwoCuspForms M H p
local notation "F̄" => qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))

private theorem _root_.ModularCurve.LinAuxD.Gamma1_le_GammaH : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro g hg
  rw [CongruenceSubgroup.Gamma1_mem] at hg
  obtain ⟨h00, h11, h10⟩ := hg
  have hg0 : g ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hg0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨g, hg0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

p2m_export "ModularCurve.LinAuxD" "Gamma1_le_GammaH"

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have h1 : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    show (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M)).strictPeriods
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples _
  rw [Subgroup.mem_strictPeriods_iff] at h1 ⊢
  exact Subgroup.map_mono (Gamma1_le_GammaH M H) h1

theorem qExpansion_coe_add (f g : CuspForm Γ 2) :
    UpperHalfPlane.qExpansion 1 ⇑(f + g) = UpperHalfPlane.qExpansion 1 ⇑f + UpperHalfPlane.qExpansion 1 ⇑g :=
  ModularFormClass.qExpansion_add one_pos (one_mem_strictPeriods M H) f g

theorem qExpansion_coe_smul (c : ℂ) (f : CuspForm Γ 2) :
    UpperHalfPlane.qExpansion 1 ⇑(c • f) = c • UpperHalfPlane.qExpansion 1 ⇑f :=
  ModularFormClass.qExpansion_smul one_pos (one_mem_strictPeriods M H) c f

omit [Fact p.Prime] in

theorem isIntegralQExp_add {f g : CuspForm Γ 2} {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp ⇑f pf)
    (hg : IsIntegralQExp ⇑g pg) : IsIntegralQExp ⇑(f + g) (pf + pg) := by
  unfold IsIntegralQExp at hf hg ⊢
  rw [map_add, hf, hg, qExpansion_coe_add]

omit [Fact p.Prime] in
theorem isIntegralQExp_zsmul {f : CuspForm Γ 2} {pf : PowerSeries ℤ} (hf : IsIntegralQExp ⇑f pf) (n : ℤ) :
    IsIntegralQExp ⇑(n • f) (n • pf) := by
  unfold IsIntegralQExp at hf ⊢
  rw [map_zsmul, hf, ← Int.cast_smul_eq_zsmul ℂ n f, qExpansion_coe_smul, Int.cast_smul_eq_zsmul]

omit [Fact p.Prime] in

theorem exists_isIntegralQExp (W : ModularForm.AtkinLehnerDatum M p) (f : CuspForm Γ 2) (hf : f ∈ L) : ∃ pf : PowerSeries ℤ, IsIntegralQExp ⇑f pf := by
  induction hf using Submodule.span_induction with
  | mem f hfS =>
    have hc : ∀ n, ModularFormClass.qCoeff ⇑f n ∈ A := fun n => by
      have h := ((CuspForm.mem_twoCuspIntegralSet_iff f).mp hfS) 1 (Subring.one_mem _) W n
      simpa using h.1
    refine ⟨PowerSeries.mk fun n => toZ ⟨_, hc n⟩, ?_⟩
    rw [isIntegralQExp_iff]
    intro n
    rw [PowerSeries.coeff_mk, cast_toZ]
    rfl
  | zero => exact ⟨0, by simpa using isIntegralQExp_zero⟩
  | add f g _ _ hf hg =>
    obtain ⟨pf, hpf⟩ := hf
    obtain ⟨pg, hpg⟩ := hg
    exact ⟨pf + pg, isIntegralQExp_add M H hpf hpg⟩
  | smul a f _ hf =>
    obtain ⟨pf, hpf⟩ := hf
    refine ⟨toZ a • pf, ?_⟩
    rw [smul_eq_toZ_zsmul]
    exact isIntegralQExp_zsmul M H hpf (toZ a)

def expZ (W : ModularForm.AtkinLehnerDatum M p) (y : L) : PowerSeries ℤ := (exists_isIntegralQExp p M H W (y : CuspForm Γ 2) y.2).choose

omit [Fact p.Prime] in
theorem isIntegralQExp_expZ (W : ModularForm.AtkinLehnerDatum M p) (y : L) : IsIntegralQExp ⇑(y : CuspForm Γ 2) (expZ p M H W y) :=
  (exists_isIntegralQExp p M H W (y : CuspForm Γ 2) y.2).choose_spec

omit [Fact p.Prime] in
theorem expZ_add (W : ModularForm.AtkinLehnerDatum M p) (y y' : L) : expZ p M H W (y + y') = expZ p M H W y + expZ p M H W y' :=
  (isIntegralQExp_expZ p M H W (y + y')).unique (isIntegralQExp_add M H (isIntegralQExp_expZ p M H W y)
    (isIntegralQExp_expZ p M H W y'))

omit [Fact p.Prime] in
theorem expZ_smul (W : ModularForm.AtkinLehnerDatum M p) (a : A) (y : L) : expZ p M H W (a • y) = toZ a • expZ p M H W y := by
  refine (isIntegralQExp_expZ p M H W (a • y)).unique ?_
  have : ((a • y : L) : CuspForm Γ 2) = toZ a • (y : CuspForm Γ 2) := by
    rw [Submodule.coe_smul, smul_eq_toZ_zsmul]
  rw [this]
  exact isIntegralQExp_zsmul M H (isIntegralQExp_expZ p M H W y) (toZ a)

omit [Fact p.Prime] in
theorem cast_coeff_expZ (W : ModularForm.AtkinLehnerDatum M p) (y : L) (n : ℕ) :
    ((PowerSeries.coeff n (expZ p M H W y) : ℤ) : ℂ) = ModularFormClass.qCoeff ⇑(y : CuspForm Γ 2) n :=
  (isIntegralQExp_expZ p M H W y).coeff n

def redA : A →+* ZMod p := (Int.castRingHom (ZMod p)).comp toZHom

theorem redA_apply (a : A) : redA p a = (toZ a : ZMod p) := rfl

@[reducible] def modA : Module A (PowerSeries (ZMod p)) := Module.compHom _ (redA p)

theorem psi_aux_smul (W : ModularForm.AtkinLehnerDatum M p) (a : A) (y : L) :
    (expZ p M H W (a • y)).map (Int.castRingHom (ZMod p)) =
      letI := modA p; a • (expZ p M H W y).map (Int.castRingHom (ZMod p)) := by
  letI := modA p
  rw [expZ_smul, map_zsmul]
  show _ = redA p a • (expZ p M H W y).map (Int.castRingHom (ZMod p))
  rw [redA_apply, Int.cast_smul_eq_zsmul]

def ψ (W : ModularForm.AtkinLehnerDatum M p) : letI := modA p; L →ₗ[A] PowerSeries (ZMod p) :=
  letI := modA p
  { toFun := fun y => (expZ p M H W y).map (Int.castRingHom (ZMod p))
    map_add' := fun y y' => by rw [expZ_add, map_add]
    map_smul' := fun a y => psi_aux_smul p M H W a y }

theorem ψ_apply (W : ModularForm.AtkinLehnerDatum M p) (y : L) : letI := modA p; ψ p M H W y = (expZ p M H W y).map (Int.castRingHom (ZMod p)) := rfl

theorem smul_top_le_ker_ψ (W : ModularForm.AtkinLehnerDatum M p) : letI := modA p;
    (CuspForm.intIdeal p • ⊤ : Submodule A L) ≤ LinearMap.ker (ψ p M H W) := by
  letI := modA p
  rw [Submodule.smul_le]
  intro r hr y _
  rw [LinearMap.mem_ker, map_smul]
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  show redA p (c * (p : A)) • ψ p M H W y = 0
  have h0 : redA p (c * (p : A)) = 0 := by
    rw [map_mul, redA_apply, redA_apply, toZ_natCast, Int.cast_natCast, ZMod.natCast_self, mul_zero]
  rw [h0, zero_smul]

def φ₀add (W : ModularForm.AtkinLehnerDatum M p) : Ω₀ →+ PowerSeries (ZMod p) :=
  letI := modA p
  (((CuspForm.intIdeal p • ⊤ : Submodule A L).liftQ (ψ p M H W) (smul_top_le_ker_ψ p M H W)).toAddMonoidHom :
    (L ⧸ (CuspForm.intIdeal p • ⊤ : Submodule A L)) →+ PowerSeries (ZMod p))

def φ₀ (W : ModularForm.AtkinLehnerDatum M p) : Ω₀ →ₗ[ZMod p] PowerSeries (ZMod p) :=
  (φ₀add p M H W).toZModLinearMap p

theorem φ₀_reduce (W : ModularForm.AtkinLehnerDatum M p) (y : L) :
    φ₀ p M H W (CuspForm.intTwoCuspReduce M H p y) = (expZ p M H W y).map (Int.castRingHom (ZMod p)) := rfl

theorem diffQExp_ρ_tmul_reduce (W : ModularForm.AtkinLehnerDatum M p)
    {ρ : K ⊗[ZMod p] Ω₀ →ₗ[K] Ω[F̄⁄K]} (hρ : IsInfReductionMap K p M H hpM ρ) (y : L) :
    diffQExp F̄ (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y)) = intSeriesC K (expZ p M H W y) := by

  suffices h : ∃ pf : PowerSeries ℤ, IsIntegralQExp ⇑(y : CuspForm Γ 2) pf ∧
      diffQExp F̄ (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y)) = intSeriesC K pf by
    obtain ⟨pf, hpf, h⟩ := h
    rw [h, (isIntegralQExp_expZ p M H W y).unique hpf]
  obtain ⟨f, hf⟩ := y
  induction hf using Submodule.span_induction with
  | mem f hfS =>
    have hc : ∀ n, ModularFormClass.qCoeff ⇑f n ∈ A := fun n => by
      have h := ((CuspForm.mem_twoCuspIntegralSet_iff f).mp hfS) 1 (Subring.one_mem _) W n
      simpa using h.1
    have hpf : IsIntegralQExp ⇑f (PowerSeries.mk fun n => toZ ⟨_, hc n⟩) := by
      rw [isIntegralQExp_iff]
      intro n
      rw [PowerSeries.coeff_mk, cast_toZ]
      rfl
    exact ⟨_, hpf, hρ f hfS _ hpf⟩
  | zero =>
    refine ⟨0, by simpa using isIntegralQExp_zero, ?_⟩
    have : (⟨0, Submodule.zero_mem _⟩ : L) = 0 := rfl
    rw [this, map_zero, TensorProduct.tmul_zero, map_zero, map_zero, intSeriesC_zero]
  | add f g hf' hg' hf hg =>
    obtain ⟨pf, hpf, hf⟩ := hf
    obtain ⟨pg, hpg, hg⟩ := hg
    refine ⟨pf + pg, isIntegralQExp_add M H hpf hpg, ?_⟩
    have : (⟨f + g, Submodule.add_mem _ hf' hg'⟩ : L) = ⟨f, hf'⟩ + ⟨g, hg'⟩ := rfl
    rw [this, map_add, TensorProduct.tmul_add, map_add, map_add, hf, hg]
    simp [intSeriesC]
  | smul a f hf' hf =>
    obtain ⟨pf, hpf, hf⟩ := hf
    refine ⟨toZ a • pf, ?_, ?_⟩
    · have : ((⟨a • f, Submodule.smul_mem _ a hf'⟩ : L) : CuspForm Γ 2) = toZ a • f := smul_eq_toZ_zsmul a f
      rw [this]
      exact isIntegralQExp_zsmul M H hpf (toZ a)
    · have h1 : (⟨a • f, Submodule.smul_mem _ a hf'⟩ : L) = toZ a • ⟨f, hf'⟩ := by
        apply Subtype.ext
        show a • f = ((toZ a • (⟨f, hf'⟩ : L) : L) : CuspForm Γ 2)
        rw [Submodule.coe_smul_of_tower]
        exact smul_eq_toZ_zsmul a f
      rw [h1, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod p) (toZ a), TensorProduct.tmul_smul,
        ← algebraMap_smul K ((toZ a : ℤ) : ZMod p), map_smul, LinearMap.map_smul_of_tower, hf, map_intCast,
        Int.cast_smul_eq_zsmul]
      simp only [intSeriesC, map_zsmul]

theorem main (W : ModularForm.AtkinLehnerDatum M p) {ρ : K ⊗[ZMod p] Ω₀ →ₗ[K] Ω[F̄⁄K]} (hρ : IsInfReductionMap K p M H hpM ρ)
    (x : K ⊗[ZMod p] Ω₀) (hx : ρ x = 0) :
    x ∈ Submodule.span K {z : K ⊗[ZMod p] Ω₀ |
      ∃ y : L, (∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑(y : CuspForm Γ 2)) n = (p : ℂ) * m) ∧
        z = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y} := by

  have hTG : ∀ z : K ⊗[ZMod p] Ω₀, diffQExp F̄ (ρ z) =
      (ιL p K ∘ₗ LinearMap.lTensor K (ofPS p)) (LinearMap.lTensor K (φ₀ p M H W) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      obtain ⟨y, rfl⟩ := CuspForm.intTwoCuspReduce_surjective M H p m
      have hc1 : c ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y =
          c • ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.lTensor_tmul, ι_tmul, φ₀_reduce, hc1, map_smul, LinearMap.map_smul_of_tower,
        diffQExp_ρ_tmul_reduce p M hpM H K W hρ y]
      congr 1
      rw [intSeriesC, ← RingHom.comp_apply (PowerSeries.map (algebraMap (ZMod p) K))
          (PowerSeries.map (Int.castRingHom (ZMod p))) (expZ p M H W y), ← PowerSeries.map_comp,
        RingHom.ext_int ((algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p))) (Int.castRingHom K)]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  have hG : (ιL p K ∘ₗ LinearMap.lTensor K (ofPS p)) (LinearMap.lTensor K (φ₀ p M H W) x) = 0 := by
    rw [← hTG, hx, map_zero]
  have hker : LinearMap.lTensor K (φ₀ p M H W) x = 0 :=
    (ι_injective p K) (by rw [map_zero]; exact hG)

  have hexact := Module.Flat.lTensor_exact K (LinearMap.exact_subtype_ker_map (φ₀ p M H W))
  obtain ⟨w, hw⟩ := (hexact x).mp hker
  rw [← hw]
  clear hw hker hG hx
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul c k =>
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    obtain ⟨y, hy⟩ := CuspForm.intTwoCuspReduce_surjective M H p (k : Ω₀)
    have hc1 : c ⊗ₜ[ZMod p] (k : Ω₀) = c • ((1 : K) ⊗ₜ[ZMod p] (k : Ω₀)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc1]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨y, ?_, by rw [hy]⟩)
    intro n
    have hk : φ₀ p M H W (k : Ω₀) = 0 := LinearMap.mem_ker.mp k.2
    rw [← hy, φ₀_reduce] at hk
    have hn : ((PowerSeries.coeff n (expZ p M H W y) : ℤ) : ZMod p) = 0 := by
      have := congrArg (PowerSeries.coeff n) hk
      rwa [PowerSeries.coeff_map, map_zero, eq_intCast] at this
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hn
    refine ⟨m, ?_⟩
    rw [← cast_coeff_expZ p M H W y n, hm]
    push_cast
    ring
  | add w₁ w₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂

end Main

end ModularCurve.LinAuxD

end

open _root_.ModularCurve _root_.P2MW.S_CuspForm_forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap.ModularCurve ModularCurve.LinAuxD in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]
    (W : ModularForm.AtkinLehnerDatum M p)
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (hex : ∃ ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
      ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (d : (ZMod M)ˣ)
    (y : CuspForm (CohCarrier.GammaH M H) 2) (hy : y ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))
    (h0 : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑y) n = (p : ℂ) * m) :
    ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d y)) n = (p : ℂ) * m := by
  classical
  obtain ⟨ρ, hρ⟩ := hex
  haveI : NeZero (M / p) := ⟨Nat.div_ne_zero_iff_of_dvd hpM |>.mpr ⟨NeZero.ne M, (Fact.out : p.Prime).ne_zero⟩⟩

  let yL : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) := ⟨y, hy⟩
  have hdmem : CuspForm.diamondLinH 2 d y ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) :=
    CuspForm.heckeRingH_apply_mem_twoCuspLattice (CuspForm.heckeGenH_mem_heckeRingH (∅ : Set ℕ) 2 (CohCarrier.Gen.dia d)) hy
  let ydL : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) := ⟨CuspForm.diamondLinH 2 d y, hdmem⟩

  have hT0 : diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p yL)) = 0 := by
    rw [diffQExp_ρ_tmul_reduce p M hpM H K W hρ yL, intSeriesC]
    have hmap : (expZ p M H W yL).map (Int.castRingHom K) = 0 := by
      ext n
      rw [PowerSeries.coeff_map, map_zero]
      obtain ⟨m, hm⟩ := h0 n
      have hc := cast_coeff_expZ p M H W yL n
      rw [hm] at hc
      have hz : (PowerSeries.coeff n (expZ p M H W yL) : ℤ) = p * m := by exact_mod_cast hc
      rw [hz, eq_intCast, Int.cast_mul, Int.cast_natCast]
      have hp0 : (p : K) = 0 := by
        rw [← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_self, map_zero]
      rw [hp0, zero_mul]
    rw [hmap, map_zero]

  have hρ0 : ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p yL) = 0 := by
    have hT : ModularGroup.T ∈ CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) :=
      ModularCurve.Gamma1_le_GammaH (M / p) _ (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
    apply ModularCurve.diffQExp_qExpFunctionFieldC_injective K _ hT
    rw [hT0, map_zero]

  have hρd : ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p ydL) = 0 := by
    have hcomp := ModularCurve.IsInfReductionMap.comp_baseChange_genDia_eq_genDiffModL_comp p M hpM hpM2 H hHp K (∅ : Set ℕ) hρ d
    have happ := LinearMap.congr_fun hcomp ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p yL)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul, hρ0, map_zero] at happ
    have hred : CuspForm.intTwoCuspGenMod M H p (∅ : Set ℕ) (CohCarrier.Gen.dia d) (CuspForm.intTwoCuspReduce M H p yL) =
        CuspForm.intTwoCuspReduce M H p ydL := rfl
    rw [hred] at happ
    exact happ

  have hTd := diffQExp_ρ_tmul_reduce p M hpM H K W hρ ydL
  rw [hρd, map_zero, intSeriesC] at hTd
  intro n
  have hc := congrArg (fun s : LaurentSeries K => s.coeff (n : ℤ)) hTd
  simp only [HahnSeries.coeff_zero] at hc
  rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast] at hc

  have hdvd : (p : ℤ) ∣ PowerSeries.coeff n (expZ p M H W ydL) := by
    have hz : ((PowerSeries.coeff n (expZ p M H W ydL) : ℤ) : ZMod p) = 0 := by
      apply (algebraMap (ZMod p) K).injective
      rw [map_zero, map_intCast]
      exact hc.symm
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, ?_⟩
  rw [← cast_coeff_expZ p M H W ydL n, hm]
  push_cast
  ring

end S_CuspForm_forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap
end P2MW
export P2MW.S_CuspForm_forall_qCoeff_diamondLinH_eq_mul_of_forall_qCoeff_eq_mul_of_exists_isInfReductionMap (solution)

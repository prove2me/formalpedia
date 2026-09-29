-- Prove2me | solution 1 for CuspForm.map_eq_zero_of_qExpansion_alSlash_diamond_of_coe_eq_smul_alSlash_diamond_of_forall_dvd_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2369630d-1a6f-58e0-9c91-a7be3e717982

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_CuspForm_map_eq_zero_of_qExpansion_smul_alSlash_diamond_of_forall_dvd_coeff_of_mem_twoCuspIntegralSet
import Theorems.Thm_CuspForm_mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Theorems.Thm_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_map_eq_zero_of_qExpansion_alSlash_diamond_of_coe_eq_smul_alSlash_diamond_of_forall_dvd_coeff
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one"
p2m_attr_erase "simp" "Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ModularForm

namespace CuspForm
p2m_export "CuspForm" "ext heckeGenH_dia heckeRingH heckeGenH_mem_heckeRingH twoCuspIntegralSet heckeRingH_apply_mem_twoCuspIntegralSet gammaLift gamma0Units_gammaLift diamondLinH coe_diamondLinH_apply coe_diamondLinH_eq_slash map_eq_zero_of_qExpansion_smul_alSlash_diamond_of_forall_dvd_coeff_of_mem_twoCuspIntegralSet mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem exists_GammaH_coe_eq_alSlash stableD exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH"
namespace KerStabZero
p2m_open "CuspForm"

open CongruenceSubgroup CohCarrier

section Algebra

def swap₀₀ (p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t : ℤ) : ℤ :=
  a * a₂ * g₀₀ * p * q - a * b * g₀₀ * p * q - a * b * p * q^2 * t + a * b₂ * p^2 * q * t -
  a₂ * b * g₀₀ * p * q - a₂ * g₀₁ * p^2 * q + a₂ * g₀₁ * p * q^2 + b^2 * g₀₀ * p * q +
  b^2 * p * q^2 * t - b * b₂ * p^2 * q * t + b * g₀₁ * p^2 * q - b * g₀₁ * p * q^2 + b * g₁₁ * p * q
  - b * g₁₁ * q^2 - b₂ * g₁₁ * p^2 + b₂ * g₁₁ * p * q

def swap₀₁ (p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t : ℤ) : ℤ :=
  -a * a₂ * b₂ * g₀₀ * p + a * b * b₂ * g₀₀ * p + a * b * b₂ * p * q * t - a * b₂^2 * p^2 * t +
  a₂^2 * b * g₀₀ * q + a₂^2 * g₀₁ * p * q - a₂ * b^2 * g₀₀ * q - a₂ * b^2 * q^2 * t +
  a₂ * b * b₂ * p * q * t - a₂ * b * g₀₁ * p * q - a₂ * b * g₁₁ * q - a₂ * b₂ * g₀₁ * p * q +
  a₂ * b₂ * g₁₁ * p + b * b₂ * g₀₁ * p * q + b * b₂ * g₁₁ * q - b₂^2 * g₁₁ * p

def swap₁₀ (p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t : ℤ) : ℤ :=
  a^2 * g₀₀ * p + a^2 * p * q * t - a * a₂ * g₀₀ * q - a * b * g₀₀ * p - a * b * p * q * t -
  a * b₂ * p * q * t - a * g₀₁ * p^2 + a * g₀₁ * p * q - a * g₁₁ * p + a * g₁₁ * q +
  a₂ * b * g₀₀ * q + a₂ * g₀₁ * p * q - a₂ * g₀₁ * q^2 + b * b₂ * p * q * t + b₂ * g₁₁ * p -
  b₂ * g₁₁ * q

def swap₁₁ (p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t : ℤ) : ℤ :=
  -a^2 * b₂ * g₀₀ * p^2 - a^2 * b₂ * p^2 * q * t + a * a₂ * b * g₀₀ * p * q +
  a * a₂ * b * p * q^2 * t + a * a₂ * b₂ * g₀₀ * p * q + a * a₂ * g₀₁ * p^2 * q +
  a * a₂ * g₁₁ * p * q + a * b₂^2 * p^2 * q * t - a * b₂ * g₀₁ * p^2 * q - a * b₂ * g₁₁ * p * q -
  a₂^2 * b * g₀₀ * q^2 - a₂^2 * g₀₁ * p * q^2 - a₂ * b * b₂ * p * q^2 * t + a₂ * b₂ * g₀₁ * p * q^2
  - a₂ * b₂ * g₁₁ * p * q + b₂^2 * g₁₁ * p * q

def swapMat (p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![swap₀₀ p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t, swap₀₁ p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t;
     p * q * swap₁₀ p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t, swap₁₁ p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t]

theorem swap_identity (p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t : ℤ) (h₁ : p * a - q * b = 1)
    (h₂ : q * a₂ - p * b₂ = 1) :
    !![q * a₂, b₂; q * p, q] * !![g₀₀, g₀₁; p * q * t, g₁₁] * !![p * a, b; p * q, p] =
      !![p * a, b; p * q, p] * swapMat p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t * !![q * a₂, b₂; q * p, q] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [swapMat, swap₀₀, swap₀₁, swap₁₀, swap₁₁, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
  · linear_combination
      (-a * a₂^2 * g₀₀ * p * q^2 + a * a₂ * b₂ * g₀₀ * p^2 * q - a * a₂ * b₂ * p^2 * q^2 * t +
      a * b₂^2 * p^3 * q * t - a₂^2 * g₀₀ * q^2 - a₂^2 * g₀₁ * p * q^3 + a₂ * b₂ * g₀₀ * p * q +
      a₂ * b₂ * g₀₁ * p^2 * q^2 - a₂ * b₂ * g₁₁ * p * q^2 - a₂ * b₂ * p * q^2 * t + a₂ * g₀₀ * q +
      b₂^2 * g₁₁ * p^2 * q + b₂^2 * p^2 * q * t + b₂ * p * q * t) * h₁ + (-a₂ * b * g₀₀ * q^2 -
      a₂ * g₀₀ * q - a₂ * g₀₁ * p * q^2 - b * b₂ * p * q^2 * t - b₂ * g₁₁ * p * q -
      b₂ * p * q * t) * h₂
  · linear_combination
      (-a₂^2 * b * g₀₀ * q^2 - a₂^2 * g₀₁ * p * q^2 + a₂ * b * b₂ * g₀₀ * p * q -
      a₂ * b * b₂ * p * q^2 * t + a₂ * b₂ * g₀₁ * p^2 * q - a₂ * b₂ * g₁₁ * p * q +
      b * b₂^2 * p^2 * q * t + b₂^2 * g₁₁ * p^2) * h₁ + (-a₂ * b * g₀₀ * q - a₂ * g₀₁ * p * q -
      b * b₂ * p * q * t - b₂ * g₁₁ * p) * h₂
  · linear_combination
      (-a * a₂ * g₀₀ * p^2 * q^2 - a * a₂ * p^2 * q^3 * t + a * b₂ * g₀₀ * p^3 * q +
      a * b₂ * p^3 * q^2 * t - a₂ * g₀₀ * p * q^2 - a₂ * g₀₁ * p^2 * q^3 - a₂ * g₁₁ * p * q^3 -
      a₂ * p * q^3 * t + b₂ * g₀₀ * p^2 * q + b₂ * g₀₁ * p^3 * q^2 + b₂ * g₁₁ * p^2 * q^2 +
      b₂ * p^2 * q^2 * t + g₀₀ * p * q + p * q^2 * t) * h₁ + (-b * g₀₀ * p * q^2 - b * p * q^3 * t
      - g₀₀ * p * q - g₀₁ * p^2 * q^2 - g₁₁ * p * q^2 - p * q^2 * t) * h₂
  · linear_combination
      (-a₂ * b * g₀₀ * p * q^2 - a₂ * b * p * q^3 * t - a₂ * g₀₁ * p^2 * q^2 - a₂ * g₁₁ * p * q^2 +
      b * b₂ * g₀₀ * p^2 * q + b * b₂ * p^2 * q^2 * t + b₂ * g₀₁ * p^3 * q +
      b₂ * g₁₁ * p^2 * q) * h₁ + (-b * g₀₀ * p * q - b * p * q^2 * t - g₀₁ * p^2 * q -
      g₁₁ * p * q) * h₂

theorem det_swapMat (p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t : ℤ) (h₁ : p * a - q * b = 1)
    (h₂ : q * a₂ - p * b₂ = 1) (h₃ : g₀₀ * g₁₁ - g₀₁ * (p * q * t) = 1) :
    (swapMat p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t).det = 1 := by
  rw [swapMat, Matrix.det_fin_two_of]
  simp only [swap₀₀, swap₀₁, swap₁₀, swap₁₁]
  linear_combination
    (a * a₂^2 * g₀₀ * g₁₁ * p * q^2 - a * a₂^2 * g₀₁ * p^2 * q^3 * t -
    2 * a * a₂ * b₂ * g₀₀ * g₁₁ * p^2 * q + 2 * a * a₂ * b₂ * g₀₁ * p^3 * q^2 * t +
    a * b₂^2 * g₀₀ * g₁₁ * p^3 - a * b₂^2 * g₀₁ * p^4 * q * t - a₂^2 * b * g₀₀ * g₁₁ * q^3 +
    a₂^2 * b * g₀₁ * p * q^4 * t + a₂^2 * g₀₀ * g₁₁ * q^2 - a₂^2 * g₀₁ * p * q^3 * t +
    2 * a₂ * b * b₂ * g₀₀ * g₁₁ * p * q^2 - 2 * a₂ * b * b₂ * g₀₁ * p^2 * q^3 * t -
    2 * a₂ * b₂ * g₀₀ * g₁₁ * p * q + 2 * a₂ * b₂ * g₀₁ * p^2 * q^2 * t -
    b * b₂^2 * g₀₀ * g₁₁ * p^2 * q + b * b₂^2 * g₀₁ * p^3 * q^2 * t + b₂^2 * g₀₀ * g₁₁ * p^2 -
    b₂^2 * g₀₁ * p^3 * q * t) * h₁ + (a₂ * g₀₀ * g₁₁ * q - a₂ * g₀₁ * p * q^2 * t -
    b₂ * g₀₀ * g₁₁ * p + b₂ * g₀₁ * p^2 * q * t + g₀₀ * g₁₁ - g₀₁ * p * q * t) * h₂ + (1) * h₃

theorem swapMat_one_zero (p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t : ℤ) :
    swapMat p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t 1 0 = p * q * swap₁₀ p q a b a₂ b₂ g₀₀ g₀₁ g₁₁ t := by
  simp [swapMat]

end Algebra

section Datum

variable {M : ℕ} [NeZero M] {p : ℕ} [Fact p.Prime]

theorem R_eq (W : ModularForm.AtkinLehnerDatum M p) : W.R = M / p := by
  have hp : p.Prime := Fact.out
  calc W.R = p * W.R / p := (Nat.mul_div_cancel_left _ hp.pos).symm
    _ = M / p := by rw [← W.hM]

theorem div_pos_of_dvd (hpM : p ∣ M) : 0 < M / p :=
  Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos

theorem Rd_eq (hpM : p ∣ M) (Wd : ModularForm.AtkinLehnerDatum M (M / p)) : Wd.R = p := by
  have h1 : (M / p) * Wd.R = (M / p) * p := by
    rw [← Wd.hM]; exact (Nat.div_mul_cancel hpM).symm
  exact Nat.eq_of_mul_eq_mul_left (div_pos_of_dvd hpM) h1

theorem unitsMap_R_eq_one_iff (hpM : p ∣ M) (W : ModularForm.AtkinLehnerDatum M p) (u : (ZMod M)ˣ) :
    ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 ↔ ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 := by
  have key : ∀ (R : ℕ) (hR : R ∣ M), R = M / p →
      (ZMod.unitsMap hR u = 1 ↔ ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1) := by
    intro R hR h; subst h; exact Iff.rfl
  exact key W.R _ (R_eq W)

theorem hHp_R {H : Subgroup (ZMod M)ˣ} (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) :
    ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H :=
  fun u hu => hHp u ((unitsMap_R_eq_one_iff hpM W u).mp hu)

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem exists_swap (hpM : p ∣ M) (Wp : ModularForm.AtkinLehnerDatum M p)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      Wd.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ * Wp.alGL =
        Wp.alGL * Matrix.SpecialLinearGroup.mapGL ℝ δ * Wd.alGL := by
  have hp : p.Prime := Fact.out
  have hMpq : (M : ℤ) = (p : ℤ) * ((M / p : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hpM).symm
  have hRp : (Wp.R : ℤ) = ((M / p : ℕ) : ℤ) := by exact_mod_cast R_eq Wp
  have hRd : (Wd.R : ℤ) = (p : ℤ) := by exact_mod_cast Rd_eq hpM Wd

  have h10 : ((M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp (Gamma0_mem.mp hγ)
  obtain ⟨t, ht⟩ := h10
  have hdetγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ((p : ℤ) * ((M / p : ℕ) : ℤ) * t) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, ht, hMpq] at h
    linear_combination h
  have h₁ : (p : ℤ) * Wp.a - ((M / p : ℕ) : ℤ) * Wp.b = 1 := by rw [← hRp]; exact Wp.bezout
  have h₂ : ((M / p : ℕ) : ℤ) * Wd.a - (p : ℤ) * Wd.b = 1 := by rw [← hRd]; exact Wd.bezout

  set δM : Matrix (Fin 2) (Fin 2) ℤ := swapMat (p : ℤ) ((M / p : ℕ) : ℤ) Wp.a Wp.b Wd.a Wd.b
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) t
    with hδM
  have hdet : δM.det = 1 := det_swapMat _ _ _ _ _ _ _ _ _ _ h₁ h₂ hdetγ
  let δ : SL(2, ℤ) := ⟨δM, hdet⟩
  have hδ0 : δ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show (((δM 1 0 : ℤ) : ZMod M) = 0)
    rw [hδM, swapMat_one_zero, ← hMpq]
    push_cast
    simp

  have hγeta : (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
         (p : ℤ) * ((M / p : ℕ) : ℤ) * t, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1] := by
    conv_lhs => rw [Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)]
    rw [ht, hMpq]
  have hPmat : Wp.mat = !![(p : ℤ) * Wp.a, Wp.b; (p : ℤ) * ((M / p : ℕ) : ℤ), (p : ℤ)] := by
    rw [ModularForm.AtkinLehnerDatum.mat, hRp]
  have hDmat : Wd.mat = !![((M / p : ℕ) : ℤ) * Wd.a, Wd.b; ((M / p : ℕ) : ℤ) * (p : ℤ), ((M / p : ℕ) : ℤ)] := by
    rw [ModularForm.AtkinLehnerDatum.mat, hRd]
  have hint : Wd.mat * (γ : Matrix (Fin 2) (Fin 2) ℤ) * Wp.mat = Wp.mat * δM * Wd.mat := by
    rw [hγeta, hPmat, hDmat, hδM]
    exact swap_identity _ _ _ _ _ _ _ _ _ _ h₁ h₂
  refine ⟨δ, hδ0, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, mapGL_coe_eq]
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hint]

end Datum

section Forms

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {p : ℕ} [Fact p.Prime]

theorem diamondLinH_diamondLinH (k : ℤ) (d e : (ZMod M)ˣ) (g : CuspForm (GammaH M H) k) :
    CuspForm.diamondLinH k d (CuspForm.diamondLinH k e g) = CuspForm.diamondLinH k (e * d) g := by
  have hD := CuspForm.stableD M H k
  refine DFunLike.ext' ?_
  rw [CuspForm.coe_diamondLinH_apply k hD d, CuspForm.coe_diamondLinH_apply k hD e, ← SlashAction.slash_mul,
    ← map_mul]
  have : ((CuspForm.gammaLift M e : Gamma0 M) : SL(2, ℤ)) *
        ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)) =
      ((CuspForm.gammaLift M e * CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)) := rfl
  rw [this, CuspForm.coe_diamondLinH_eq_slash k hD (e * d) (CuspForm.gammaLift M e * CuspForm.gammaLift M d)
    (by rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift])]

theorem diamondLinH_mem_heckeRingH (k : ℤ) (d : (ZMod M)ˣ) :
    (CuspForm.diamondLinH k d : CuspForm (GammaH M H) k →ₗ[ℂ] CuspForm (GammaH M H) k) ∈
      CuspForm.heckeRingH M H k := by
  have h := CuspForm.heckeGenH_mem_heckeRingH (H := H) (∅ : Set ℕ) k (.dia d)
  rwa [CuspForm.heckeGenH_dia] at h

theorem exists_coe_diamondLinH_eq_alSlash_diamondLinH {q : ℕ} (W : ModularForm.AtkinLehnerDatum M q)
    (k : ℤ) (d : (ZMod M)ˣ) (g X : CuspForm (GammaH M H) k) (hX : ⇑X = ModularForm.alSlash W k ⇑g) :
    ∃ δ : (ZMod M)ˣ, ⇑(CuspForm.diamondLinH k d X) = ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k δ g) := by
  have hD := CuspForm.stableD M H k
  obtain ⟨δ, hδ, hW⟩ := W.exists_mem_Gamma0_alGL_mul_eq (g := ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)))
    (CuspForm.gammaLift M d).2
  refine ⟨CohCarrier.gamma0Units M ⟨δ, hδ⟩, ?_⟩
  rw [CuspForm.coe_diamondLinH_apply k hD d X, hX, ModularForm.alSlash_def, ModularForm.alSlash_def,
    ← SlashAction.slash_mul, hW, SlashAction.slash_mul, CuspForm.coe_diamondLinH_eq_slash k hD _ ⟨δ, hδ⟩ rfl g]

theorem mem_twoCuspIntegralSet_of_coe_eq_alSlash (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wp : ModularForm.AtkinLehnerDatum M p) (f : CuspForm (GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (Y : CuspForm (GammaH M H) 2) (hY : ⇑Y = ModularForm.alSlash Wp 2 ⇑f) :
    Y ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
  refine CuspForm.mem_twoCuspIntegralSet_of_forall_qCoeff_diamondLinH_mem p M hpM hpM2 H hHp Y ?_
  intro d W' n
  obtain ⟨δ, hδ⟩ := exists_coe_diamondLinH_eq_alSlash_diamondLinH Wp 2 d f Y hY
  refine ⟨?_, ?_⟩
  · rw [hδ]
    exact (hf _ (diamondLinH_mem_heckeRingH 2 δ) Wp n).2
  · obtain ⟨δ', hδ'⟩ := CuspForm.exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH M p hpM H hHp W' Wp 2
      (CuspForm.diamondLinH 2 δ f)
    have h1 : ((p : ℂ) ^ ((2 : ℤ) - 2)) = 1 := by norm_num
    rw [hδ, hδ', h1, one_smul, diamondLinH_diamondLinH]
    exact (hf _ (diamondLinH_mem_heckeRingH 2 (δ * δ')) W' n).1

theorem smul_slash_mapGL (k : ℤ) (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (c : ℂ) :
    (c • F) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      c • (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) :=
  ModularForm.SL_smul_slash k γ F c

end Forms

end CuspForm.KerStabZero

open CuspForm.KerStabZero in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wp : ModularForm.AtkinLehnerDatum M p) (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (K : Type*) [Field K] (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)
    (x : CuspForm (CohCarrier.GammaH M H) 2) (hx : x ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf0 : PowerSeries ℤ) (hpf0 : ModularCurve.IsIntegralQExp (ModularForm.alSlash Wp 2 ⇑(CuspForm.diamondLinH 2 e x)) pf0)
    (hp0 : ∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n pf0)
    (D : ℕ) (g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : (⇑g : UpperHalfPlane → ℂ) = (D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e x))
    (pgW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpgW : pgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 (ModularForm.alSlash Wp 2 ⇑(CuspForm.diamondLinH 2 e g))) :
    pgW.map φ = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hD := CuspForm.stableD M H 2

  obtain ⟨Y, hY⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp Wp H (hHp_R hpM hHp Wp) 2
    (CuspForm.diamondLinH 2 e x)

  have hex : CuspForm.diamondLinH 2 e x ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (diamondLinH_mem_heckeRingH 2 e) hx
  have hYmem : Y ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    mem_twoCuspIntegralSet_of_coe_eq_alSlash hpM hpM2 hHp Wp _ hex Y hY

  have hpfY : ModularCurve.IsIntegralQExp (⇑Y) pf0 := by rw [hY]; exact hpf0

  obtain ⟨δ, hδ0, hswap⟩ := exists_swap hpM Wp Wd (CuspForm.gammaLift M e).2

  have key : ModularForm.alSlash Wp 2 ⇑(CuspForm.diamondLinH 2 e g) =
      (D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 (CohCarrier.gamma0Units M ⟨δ, hδ0⟩) Y) := by
    rw [CuspForm.coe_diamondLinH_apply 2 hD e g, hg, smul_slash_mapGL, ModularForm.alSlash_smul]
    congr 1
    rw [CuspForm.coe_diamondLinH_eq_slash 2 hD _ ⟨δ, hδ0⟩ rfl Y, hY, CuspForm.coe_diamondLinH_apply 2 hD e x,
      ModularForm.alSlash_def, ModularForm.alSlash_def, ModularForm.alSlash_def, ModularForm.alSlash_def]
    simp only [← SlashAction.slash_mul]
    congr 1
    rw [mul_assoc (Matrix.SpecialLinearGroup.mapGL ℝ ((CuspForm.gammaLift M e : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) :
        GL (Fin 2) ℝ) Wd.alGL, mul_assoc (Matrix.SpecialLinearGroup.mapGL ℝ
        ((CuspForm.gammaLift M e : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) _ Wp.alGL, hswap, ← mul_assoc,
      ← mul_assoc]
  have hpgW' : pgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2
        ⇑(CuspForm.diamondLinH 2 (CohCarrier.gamma0Units M ⟨δ, hδ0⟩) Y)) := by
    rw [hpgW, key]
  exact CuspForm.map_eq_zero_of_qExpansion_smul_alSlash_diamond_of_forall_dvd_coeff_of_mem_twoCuspIntegralSet
    p M H hpM hpM2 hHp Wd (CohCarrier.gamma0Units M ⟨δ, hδ0⟩) K φ hφ Y hYmem pf0 hpfY hp0 D pgW hpgW'

end S_CuspForm_map_eq_zero_of_qExpansion_alSlash_diamond_of_coe_eq_smul_alSlash_diamond_of_forall_dvd_coeff
end P2MW
export P2MW.S_CuspForm_map_eq_zero_of_qExpansion_alSlash_diamond_of_coe_eq_smul_alSlash_diamond_of_forall_dvd_coeff (solution)

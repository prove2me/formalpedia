-- Prove2me | solution 1 for CuspForm.exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f066c86c-c0a6-51b1-ac46-8af52566232b

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_CuspForm_exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp
import Theorems.Thm_ModularCurve_isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff
import Theorems.Thm_CuspForm_add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC
import Theorems.Thm_CuspForm_exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH
import Theorems.Thm_CuspForm_mem_twoCuspIntegralSet_of_mem_twoCuspLattice
import Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
import Theorems.Thm_ModularCurve_exists_isFrobPushDiff_qExpFunctionFieldC_gammaH
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span
import Theorems.Thm_ModularCurve_finite_ssPlacesQExp
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_kaehlerD_ne_zero_of_ord_eq_one
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet
p2m_attr_erase "instance" "ValuationSubring.instIsAlgClosedResidueField ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single"
p2m_attr_erase "simp" "ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe"
p2m_attr_erase "simp" "CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply"
p2m_attr_erase "simp" "AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

namespace PoleDescent

section Pole
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def PoleLe (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) (n : ℕ) : Prop :=
  ∃ g : F, ω = g • v.dCoord ∧ v.uniformizer ^ n * g ∈ v.toValuationSubring

theorem PoleLe.zero (v : AlgebraicCurve.Place K F) (n : ℕ) : PoleLe v 0 n :=
  ⟨0, by rw [zero_smul], by rw [mul_zero]; exact v.toValuationSubring.zero_mem⟩

theorem PoleLe.add {v : AlgebraicCurve.Place K F} {ω η : Ω[F⁄K]} {n : ℕ} (hω : PoleLe v ω n) (hη : PoleLe v η n) :
    PoleLe v (ω + η) n := by
  obtain ⟨g, rfl, hg⟩ := hω
  obtain ⟨h, rfl, hh⟩ := hη
  exact ⟨g + h, by rw [add_smul], by rw [mul_add]; exact add_mem hg hh⟩

theorem PoleLe.neg {v : AlgebraicCurve.Place K F} {ω : Ω[F⁄K]} {n : ℕ} (hω : PoleLe v ω n) : PoleLe v (-ω) n := by
  obtain ⟨g, rfl, hg⟩ := hω
  exact ⟨-g, by rw [neg_smul], by rw [mul_neg]; exact neg_mem hg⟩

theorem PoleLe.smul {v : AlgebraicCurve.Place K F} {ω : Ω[F⁄K]} {n : ℕ} (c : K) (hω : PoleLe v ω n) : PoleLe v (c • ω) n := by
  obtain ⟨g, rfl, hg⟩ := hω
  refine ⟨algebraMap K F c * g, by rw [mul_smul, algebraMap_smul], ?_⟩
  rw [mul_left_comm]
  exact mul_mem (v.algebraMap_mem' c) hg

theorem PoleLe.mono {v : AlgebraicCurve.Place K F} {ω : Ω[F⁄K]} {m n : ℕ} (h : m ≤ n) (hω : PoleLe v ω m) : PoleLe v ω n := by
  obtain ⟨g, rfl, hg⟩ := hω
  refine ⟨g, rfl, ?_⟩
  rw [← Nat.sub_add_cancel h, pow_add, mul_assoc]
  exact mul_mem (pow_mem v.uniformizer_mem_toValuationSubring _) hg

theorem PoleLe.of_isRegularAt {v : AlgebraicCurve.Place K F} {ω : Ω[F⁄K]} (h : v.IsRegularAt ω) (n : ℕ) : PoleLe v ω n := by
  obtain ⟨g, hg, rfl⟩ := h
  exact PoleLe.mono (Nat.zero_le n) ⟨g, rfl, by rw [pow_zero, one_mul]; exact hg⟩

theorem PoleLe.hasSimplePoleAt {v : AlgebraicCurve.Place K F} {ω : Ω[F⁄K]} (h : PoleLe v ω 1) : v.HasSimplePoleAt ω := by
  obtain ⟨g, rfl, hg⟩ := h
  exact ⟨g, by rw [pow_one] at hg; exact hg, rfl⟩

theorem PoleLe.of_add_isRegularAt {v : AlgebraicCurve.Place K F} {η ω' : Ω[F⁄K]} {n : ℕ}
    (hreg : v.IsRegularAt (η + ω')) (hη : PoleLe v η n) : PoleLe v ω' n := by
  have : ω' = (η + ω') + -η := by abel
  rw [this]
  exact (PoleLe.of_isRegularAt hreg n).add hη.neg

theorem PoleLe.sum {v : AlgebraicCurve.Place K F} {ι : Type*} (s : Finset ι) (ω : ι → Ω[F⁄K]) {n : ℕ}
    (h : ∀ i ∈ s, PoleLe v (ω i) n) : PoleLe v (∑ i ∈ s, ω i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact PoleLe.zero v n
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exists_poleLe [AlgebraicCurve.IsCurveOver K F] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) : ∃ n : ℕ, PoleLe v ω n := by

  set π : v.toValuationSubring := ⟨v.uniformizer, v.uniformizer_mem_toValuationSubring⟩ with hπdef
  have hπ : Irreducible π := v.irreducible_mk_uniformizer
  have hord : v.ord v.uniformizer = 1 := v.ord_coe_irreducible hπ
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.IsAlgebraic.of_finite _ _
  have hD : v.dCoord ≠ 0 := AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one x v hord
  have h1 : Module.finrank F Ω[F⁄K] = 1 := AlgebraicCurve.IsCurveOver.finrank_kaehler
  obtain ⟨g, hg⟩ := (finrank_eq_one_iff_of_nonzero' v.dCoord hD).mp h1 ω
  by_cases hg0 : g = 0
  · exact ⟨0, g, hg.symm, by rw [hg0, mul_zero]; exact v.toValuationSubring.zero_mem⟩
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hg0 hπ
  refine ⟨(-v.ord g).toNat, g, hg.symm, ?_⟩
  have hπ0 : ((π : v.toValuationSubring) : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hg' : g = ((u : v.toValuationSubring) : F) * ((π : v.toValuationSubring) : F) ^ (v.ord g) := hu
  generalize v.ord g = m at hg' ⊢
  have hk : (0 : ℤ) ≤ ((-m).toNat : ℤ) + m := by omega
  obtain ⟨k, hk'⟩ := Int.eq_ofNat_of_zero_le hk
  have key : v.uniformizer ^ (-m).toNat * g = ((u : v.toValuationSubring) : F) * ((π : v.toValuationSubring) : F) ^ k := by
    rw [hg', mul_left_comm, show v.uniformizer = ((π : v.toValuationSubring) : F) from rfl, ← zpow_natCast,
      ← zpow_add₀ hπ0, hk', zpow_natCast]
  rw [key]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 k)

end Pole

section Book

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem analyticAt_cuspFunction_one (f : CuspForm (CohCarrier.GammaH M H) 2) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    (by rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH M H)]
        exact AddSubgroup.mem_zmultiples _)

theorem qExpansion_sub (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    UpperHalfPlane.qExpansion 1 ⇑(f - g) = UpperHalfPlane.qExpansion 1 ⇑f - UpperHalfPlane.qExpansion 1 ⇑g := by
  rw [sub_eq_add_neg, CuspForm.coe_add, UpperHalfPlane.qExpansion_add (analyticAt_cuspFunction_one f)
    (by rw [CuspForm.coe_neg]; exact (analyticAt_cuspFunction_one (-g))), CuspForm.coe_neg,
    UpperHalfPlane.qExpansion_neg (analyticAt_cuspFunction_one g), sub_eq_add_neg]

private theorem _root_.PoleDescent.qExpansion_smul (c : ℂ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    UpperHalfPlane.qExpansion 1 ⇑(c • f) = c • UpperHalfPlane.qExpansion 1 ⇑f := by
  rw [CuspForm.IsGLPos.coe_smul, UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_one f)]

p2m_export "PoleDescent" "qExpansion_smul"

theorem exists_isIntegralQExp {p : ℕ} (W : ModularForm.AtkinLehnerDatum M p) (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ pf : PowerSeries ℤ, ModularCurve.IsIntegralQExp f pf := by
  have hint : ∀ n : ℕ, ∃ m : ℤ, (m : ℂ) = ModularFormClass.qCoeff (⇑f) n := by
    intro n
    have h := ((CuspForm.mem_twoCuspIntegralSet_iff f).mp hf 1 (Subring.one_mem _) W n).1
    rw [Module.End.one_apply] at h
    exact Subring.mem_bot.mp h
  choose m hm using hint
  refine ⟨PowerSeries.mk m, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast, hm]
  rfl

theorem intSeriesC_eq_of_intTwoCuspReduce_eq (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hpM : p ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p)
    (y y' : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ))
    (hyy : CuspForm.intTwoCuspReduce M H p y = CuspForm.intTwoCuspReduce M H p y')
    (pf pf' : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp (y : CuspForm (CohCarrier.GammaH M H) 2) pf)
    (hpf' : ModularCurve.IsIntegralQExp (y' : CuspForm (CohCarrier.GammaH M H) 2) pf') :
    ModularCurve.intSeriesC K pf = ModularCurve.intSeriesC K pf' := by

  have hker : CuspForm.intTwoCuspReduce M H p (y - y') = 0 := by rw [map_sub, hyy, sub_self]
  rw [CuspForm.intTwoCuspReduce_apply] at hker
  have hmem : y - y' ∈ (CuspForm.intIdeal p • ⊤ : Submodule (⊥ : Subring ℂ) _) :=
    (CuspForm.twoCuspReduce_eq_zero_iff M H 2 p ⊥ (CuspForm.intIdeal p) (y - y')).mp hker
  rw [CuspForm.intIdeal, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  obtain ⟨pz, hpz⟩ := exists_isIntegralQExp W (z : CuspForm (CohCarrier.GammaH M H) 2)
    (CuspForm.mem_twoCuspIntegralSet_of_mem_twoCuspLattice p M hpM H hHp _ z.2)

  have hcoef : ∀ n : ℕ, PowerSeries.coeff n pf - PowerSeries.coeff n pf' = (p : ℤ) * PowerSeries.coeff n pz := by
    intro n
    apply Int.cast_injective (α := ℂ)
    have h1 := hpf.coeff n
    have h2 := hpf'.coeff n
    have h3 := hpz.coeff n
    have hsub : (((y - y' : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)) : CuspForm (CohCarrier.GammaH M H) 2))
        = ((p : (⊥ : Subring ℂ)) : ℂ) • (z : CuspForm (CohCarrier.GammaH M H) 2) := by
      rw [← hz, Submodule.coe_smul, Subring.smul_def]
    rw [Submodule.coe_sub] at hsub
    have hq := congrArg (fun F : CuspForm (CohCarrier.GammaH M H) 2 => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 ⇑F)) hsub
    rw [qExpansion_sub, map_sub, qExpansion_smul, PowerSeries.coeff_smul, smul_eq_mul] at hq
    push_cast
    rw [h1, h2, h3, hq]
    simp

  unfold ModularCurve.intSeriesC
  congr 1
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, ← sub_eq_zero, ← Int.cast_sub, hcoef n,
    Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]

theorem diamondLinH_diamondLinH (d d' : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    CuspForm.diamondLinH 2 d' (CuspForm.diamondLinH 2 d f) = CuspForm.diamondLinH 2 (d * d') f := by
  have hD := CuspForm.stableD M H 2
  apply DFunLike.coe_injective
  show ⇑(CuspForm.diamondLinH 2 d' (CuspForm.diamondLinH 2 d f)) = ⇑(CuspForm.diamondLinH 2 (d * d') f)
  rw [CuspForm.coe_diamondLinH_eq_slash 2 hD d' (CuspForm.gammaLift M d') (CuspForm.gamma0Units_gammaLift d'),
    CuspForm.coe_diamondLinH_eq_slash 2 hD d (CuspForm.gammaLift M d) (CuspForm.gamma0Units_gammaLift d),
    CuspForm.coe_diamondLinH_eq_slash 2 hD (d * d') (CuspForm.gammaLift M d * CuspForm.gammaLift M d')
      (by rw [map_mul, CuspForm.gamma0Units_gammaLift, CuspForm.gamma0Units_gammaLift]),
    ← SlashAction.slash_mul, ← map_mul, Subgroup.coe_mul]

theorem diamondLinH_one (f : CuspForm (CohCarrier.GammaH M H) 2) : CuspForm.diamondLinH 2 1 f = f := by
  have hD := CuspForm.stableD M H 2
  apply DFunLike.coe_injective
  show ⇑(CuspForm.diamondLinH 2 1 f) = ⇑f
  rw [CuspForm.coe_diamondLinH_eq_slash 2 hD 1 1 (map_one _), Subgroup.coe_one, map_one, SlashAction.slash_one]

theorem diffQExp_intCast_smul {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L)) (z : ℤ) (ω : Ω[↥F⁄L]) :
    ModularCurve.diffQExp F ((z : L) • ω) = (z : L) • ModularCurve.diffQExp F ω := by
  rw [Int.cast_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]

theorem intSeriesC_eq_sum (K : Type*) [Field K] {ι : Type*} (s : Finset ι)
    (b : ι → CuspForm (CohCarrier.GammaH M H) 2) (c : ι → ℤ)
    (y : CuspForm (CohCarrier.GammaH M H) 2) (hy : y = ∑ i ∈ s, (c i : ℂ) • b i)
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp y pf)
    (pb : ι → PowerSeries ℤ) (hpb : ∀ i ∈ s, ModularCurve.IsIntegralQExp (b i) (pb i)) :
    ModularCurve.intSeriesC K pf = ∑ i ∈ s, (c i : K) • ModularCurve.intSeriesC K (pb i) := by
  classical
  have hq : UpperHalfPlane.qExpansion 1 ⇑y = ∑ i ∈ s, (c i : ℂ) • UpperHalfPlane.qExpansion 1 ⇑(b i) := by
    rw [hy]
    clear hy hpf hpb
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add,
        UpperHalfPlane.qExpansion_add (analyticAt_cuspFunction_one _) (analyticAt_cuspFunction_one _), ← ih, qExpansion_smul]
  have hcoef : ∀ n : ℕ, PowerSeries.coeff n pf = ∑ i ∈ s, c i * PowerSeries.coeff n (pb i) := by
    intro n
    apply Int.cast_injective (α := ℂ)
    rw [hpf.coeff n, hq, map_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [PowerSeries.coeff_smul, smul_eq_mul, (hpb i hi).coeff n]
  have hpfeq : pf = ∑ i ∈ s, PowerSeries.C (c i) * pb i := by
    ext n
    rw [hcoef n, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [PowerSeries.coeff_C_mul]
  unfold ModularCurve.intSeriesC
  rw [hpfeq, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_mul, PowerSeries.map_C, eq_intCast, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem exists_unit_mul_natCast_eq_one (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) :
    ∃ e : (ZMod M)ˣ, ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 := by
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    apply hpM2
    obtain ⟨k, hk⟩ := hpM
    rw [hk, Nat.mul_div_cancel_left _ hp.pos] at h
    rw [hk, pow_two]
    exact Nat.mul_dvd_mul_left p h
  haveI : NeZero (M / p) := ⟨(Nat.div_ne_zero_iff_of_dvd hpM).mpr ⟨NeZero.ne M, hp.ne_zero⟩⟩
  obtain ⟨e, he⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) (m := M) (ZMod.unitOfCoprime p hcop)⁻¹
  refine ⟨e, ?_⟩
  rw [he]
  exact Units.inv_mul_eq_one.mpr (ZMod.coe_unitOfCoprime p hcop)

end Book

end PoleDescent

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf) :
    ∃ ω ∈ ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
      ModularCurve.diffQExp
          (ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω =
        ModularCurve.intSeriesC K pf := by
  classical
  have hp : p.Prime := Fact.out
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  haveI : NeZero (M / p) := ⟨(Nat.div_ne_zero_iff_of_dvd hpM).mpr ⟨NeZero.ne M, hp.ne_zero⟩⟩

  have hT : ModularGroup.T ∈ CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) :=
    ModularCurve.translation_mem_GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)

  obtain ⟨ω, hωreg, hωΘ⟩ :=
    CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp
      p M hpM hpM2 H hHp K f pf hpf
  refine ⟨ω, ?_, hωΘ⟩

  obtain ⟨⟨R, hMR, aW, bW, bezW⟩⟩ := ModularForm.AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd hp hpM hpM2
  have hR : R = M / p := by rw [hMR, Nat.mul_div_cancel_left R hp.pos]
  subst hR
  set W : ModularForm.AtkinLehnerDatum M p := ⟨M / p, hMR, aW, bW, bezW⟩ with hWdef
  obtain ⟨C, hC⟩ := ModularCurve.exists_isFrobPushDiff_qExpFunctionFieldC_gammaH p K (M / p) (ModularCurve.infSubgroup p M H hpM)
  obtain ⟨e, he⟩ := PoleDescent.exists_unit_mul_natCast_eq_one p M hpM hpM2
  have hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e⁻¹ : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)) := by
    rw [map_inv]
    exact (Units.eq_inv_of_mul_eq_one_left he).symm

  obtain ⟨ωW, hωW⟩ := CuspForm.exists_linearEquiv_intTwoCuspForms_intTwoCuspReduce_eq_of_coe_eq_alSlash_diamondLinH
    p M hpM hpM2 H hHp W e
  let δ : (ZMod M)ˣ → CuspForm.IntTwoCuspForms M H p →ₗ[ZMod p] CuspForm.IntTwoCuspForms M H p :=
    fun d => CuspForm.intTwoCuspGenMod M H p ∅ (.dia d)
  have hδδ : ∀ (d d' : (ZMod M)ˣ) (x : CuspForm.IntTwoCuspForms M H p), δ d' (δ d x) = δ (d * d') x := by
    intro d d' x
    obtain ⟨y, rfl⟩ := CuspForm.intTwoCuspReduce_surjective M H p x
    show CuspForm.intTwoCuspGenMod M H p ∅ (.dia d') (CuspForm.intTwoCuspGenMod M H p ∅ (.dia d) (CuspForm.intTwoCuspReduce M H p y)) =
      CuspForm.intTwoCuspGenMod M H p ∅ (.dia (d * d')) (CuspForm.intTwoCuspReduce M H p y)
    rw [CuspForm.intTwoCuspGenMod_reduce, CuspForm.intTwoCuspGenMod_reduce, CuspForm.intTwoCuspGenMod_reduce]
    congr 1
    apply Subtype.ext
    show CuspForm.diamondLinH 2 d' (CuspForm.diamondLinH 2 d (y : CuspForm (CohCarrier.GammaH M H) 2)) =
      CuspForm.diamondLinH 2 (d * d') (y : CuspForm (CohCarrier.GammaH M H) 2)
    exact PoleDescent.diamondLinH_diamondLinH d d' _
  have hδ1 : ∀ x : CuspForm.IntTwoCuspForms M H p, δ 1 x = x := by
    intro x
    obtain ⟨y, rfl⟩ := CuspForm.intTwoCuspReduce_surjective M H p x
    show CuspForm.intTwoCuspGenMod M H p ∅ (.dia 1) (CuspForm.intTwoCuspReduce M H p y) = CuspForm.intTwoCuspReduce M H p y
    rw [CuspForm.intTwoCuspGenMod_reduce]
    congr 1
    apply Subtype.ext
    exact PoleDescent.diamondLinH_one _
  let τ : CuspForm.IntTwoCuspForms M H p → CuspForm.IntTwoCuspForms M H p := fun x => δ e⁻¹ (ωW x)
  have hτ : Function.Surjective τ := by
    intro z
    refine ⟨ωW.symm (δ e z), ?_⟩
    show δ e⁻¹ (ωW (ωW.symm (δ e z))) = z
    rw [LinearEquiv.apply_symm_apply, hδδ, mul_inv_cancel, hδ1]

  have hrep : ∀ x : CuspForm.IntTwoCuspForms M H p, ∃ y : CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ),
      CuspForm.intTwoCuspReduce M H p y = x := CuspForm.intTwoCuspReduce_surjective M H p
  choose yx hyx using hrep
  have hyset : ∀ x, (yx x : CuspForm (CohCarrier.GammaH M H) 2) ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    fun x => CuspForm.mem_twoCuspIntegralSet_of_mem_twoCuspLattice p M hpM H hHp _ (yx x).2
  have hpfx : ∀ x, ∃ q : PowerSeries ℤ, ModularCurve.IsIntegralQExp (yx x : CuspForm (CohCarrier.GammaH M H) 2) q :=
    fun x => PoleDescent.exists_isIntegralQExp W _ (hyset x)
  choose pfx hpfx' using hpfx
  have hΦ : ∀ x, ∃ η : Ω[↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))⁄K],
      (∀ v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
        v ∉ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p → v.IsRegularAt η) ∧
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) η =
        ModularCurve.intSeriesC K (pfx x) :=
    fun x => CuspForm.exists_forall_isRegularAt_of_not_mem_ssPlacesQExp_diffQExp_eq_intSeriesC_of_isIntegralQExp
      p M hpM hpM2 H hHp K _ (pfx x) (hpfx' x)
  choose Φ hΦreg hΦΘ using hΦ
  have hinj := ModularCurve.diffQExp_qExpFunctionFieldC_injective K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT

  have hTCR : ∀ x, C (Φ x) + Φ (τ x) ∈ AlgebraicCurve.regularDifferentials K
      ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := by
    intro x

    obtain ⟨g, hg⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHp 2 (CuspForm.diamondLinH 2 e (yx x : CuspForm (CohCarrier.GammaH M H) 2))
    obtain ⟨hgset, hωWx⟩ := hωW _ (hyset x) g hg

    have hdgset : CuspForm.diamondLinH 2 e⁻¹ g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
      CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (CuspForm.heckeGenH_mem_heckeRingH (H := H) ∅ 2 (.dia e⁻¹)) hgset
    obtain ⟨pdh, hpdh⟩ := PoleDescent.exists_isIntegralQExp W _ hdgset

    have hclass : CuspForm.intTwoCuspReduce M H p (yx (τ x)) =
        CuspForm.intTwoCuspReduce M H p ⟨CuspForm.diamondLinH 2 e⁻¹ g, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hdgset⟩ := by
      rw [hyx]
      show δ e⁻¹ (ωW x) = _
      rw [← hyx x]
      have h1 : CuspForm.intTwoCuspReduce M H p (yx x) = CuspForm.intTwoCuspReduce M H p
          ⟨(yx x : CuspForm (CohCarrier.GammaH M H) 2), CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ (hyset x)⟩ := by
        congr 1
      rw [h1, hωWx]
      show CuspForm.intTwoCuspGenMod M H p ∅ (.dia e⁻¹) (CuspForm.intTwoCuspReduce M H p _) = _
      rw [CuspForm.intTwoCuspGenMod_reduce]
      congr 1
    have hΘ' : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (Φ (τ x)) =
        ModularCurve.intSeriesC K pdh := by
      rw [hΦΘ]
      exact PoleDescent.intSeriesC_eq_of_intTwoCuspReduce_eq K hpM hHp W (yx (τ x))
        ⟨CuspForm.diamondLinH 2 e⁻¹ g, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hdgset⟩ hclass
        (pfx (τ x)) pdh (hpfx' (τ x)) hpdh
    exact CuspForm.add_mem_regularDifferentials_of_isFrobPushDiff_of_diffQExp_eq_intSeriesC p M hpM hpM2 H hHp K W e he C hC
      _ (hyset x) g hg e⁻¹ hd (pfx x) pdh (hpfx' x) hpdh (Φ x) (Φ (τ x)) (hΦΘ x) hΘ'

  have hdesc : ∀ n : ℕ, (∀ x, ∀ v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
        PoleDescent.PoleLe v (Φ x) n) →
      (∀ x, ∀ v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
        PoleDescent.PoleLe v (Φ x) ((n + p - 1) / p)) := by
    intro n hn x v hv
    obtain ⟨x', rfl⟩ := hτ x
    obtain ⟨-, hpole⟩ := ModularCurve.isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff
      K p (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT C hC n (Φ x') (hΦreg x') (fun w hw => hn x' w hw)
    have hreg : v.IsRegularAt (C (Φ x') + Φ (τ x')) := (AlgebraicCurve.mem_regularDifferentials_iff.mp (hTCR x')) v
    exact PoleDescent.PoleLe.of_add_isRegularAt hreg (hpole v hv)

  have hinit : ∃ n₀ : ℕ, ∀ x, ∀ v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
      PoleDescent.PoleLe v (Φ x) n₀ := by

    obtain ⟨xg, -, htr, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
    haveI : AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :=
      AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
    haveI := hfd

    obtain ⟨m, b, -, -, hspan⟩ := CuspForm.exists_linearIndependent_forall_twoCuspLattice_eq_span p M hpM hpM2 H hHp
    have hbL : ∀ i, b i ∈ CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ) := fun i => by
      rw [hspan ⊥]; exact Submodule.subset_span ⟨i, rfl⟩
    let xb : Fin m → CuspForm.IntTwoCuspForms M H p := fun i => CuspForm.intTwoCuspReduce M H p ⟨b i, hbL i⟩
    have hpbi : ∀ i, ∃ q : PowerSeries ℤ, ModularCurve.IsIntegralQExp (b i) q := fun i =>
      PoleDescent.exists_isIntegralQExp W (b i) (CuspForm.mem_twoCuspIntegralSet_of_mem_twoCuspLattice p M hpM H hHp _ (hbL i))
    choose pb hpb using hpbi
    have hSS := ModularCurve.finite_ssPlacesQExp K p (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
    have hmero : ∀ (i : Fin m) (v : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
        ∃ n : ℕ, PoleDescent.PoleLe v (Φ (xb i)) n := fun i v => PoleDescent.exists_poleLe xg v _
    choose nb hnb using hmero
    refine ⟨hSS.toFinset.sup (fun v => Finset.univ.sup (fun i => nb i v)), ?_⟩
    intro x v hv

    have hyL : (yx x : CuspForm (CohCarrier.GammaH M H) 2) ∈ Submodule.span (⊥ : Subring ℂ) (Set.range b) := by
      rw [← hspan ⊥]; exact (yx x).2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (⊥ : Subring ℂ)).mp hyL
    have hcz : ∀ i, ∃ z : ℤ, (z : ℂ) = ((c i : (⊥ : Subring ℂ)) : ℂ) := fun i => Subring.mem_bot.mp (c i).2
    choose cz hcz' using hcz
    have hysum : (yx x : CuspForm (CohCarrier.GammaH M H) 2) = ∑ i, (cz i : ℂ) • b i := by
      rw [← hc]
      apply Finset.sum_congr rfl
      intro i _
      rw [Subring.smul_def, ← hcz' i]

    have hΘsum : ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (Φ x) =
        ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          (∑ i, (cz i : K) • Φ (xb i)) := by
      rw [hΦΘ x, map_sum, PoleDescent.intSeriesC_eq_sum K Finset.univ b cz _ hysum (pfx x) (hpfx' x) pb (fun i _ => hpb i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [PoleDescent.diffQExp_intCast_smul, hΦΘ (xb i)]
      congr 1
      exact PoleDescent.intSeriesC_eq_of_intTwoCuspReduce_eq K hpM hHp W ⟨b i, hbL i⟩ (yx (xb i)) (hyx (xb i)).symm
        (pb i) (pfx (xb i)) (hpb i) (hpfx' (xb i))
    have hΦx : Φ x = ∑ i, (cz i : K) • Φ (xb i) := hinj hΘsum
    rw [hΦx]
    apply PoleDescent.PoleLe.sum
    intro i _
    apply PoleDescent.PoleLe.smul
    refine (hnb i v).mono (le_trans ?_ (Finset.le_sup (f := fun v => Finset.univ.sup (fun i => nb i v)) (hSS.mem_toFinset.mpr hv)))
    exact Finset.le_sup (f := fun i => nb i v) (Finset.mem_univ i)

  obtain ⟨n₀, hn₀⟩ := hinit
  have hfinal : ∀ x, ∀ v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
      PoleDescent.PoleLe v (Φ x) 1 := by
    suffices hk : ∀ n : ℕ, (∀ x, ∀ v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
        PoleDescent.PoleLe v (Φ x) n) → ∀ x, ∀ v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,
        PoleDescent.PoleLe v (Φ x) 1 from hk n₀ hn₀
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hP
      by_cases hn : n ≤ 1
      · intro x v hv
        exact (hP x v hv).mono hn
      · have h2n : 2 ≤ n := by omega
        have h2p : 2 ≤ p := hp.two_le
        have hle : n + p ≤ n * p := by nlinarith [Nat.mul_le_mul_left n h2p, Nat.mul_le_mul_right p h2n]
        have hlt : (n + p - 1) / p < n := by
          rw [Nat.div_lt_iff_lt_mul hp.pos]
          omega
        exact ih _ hlt (hdesc n hP)

  set x₀ : CuspForm.IntTwoCuspForms M H p :=
    CuspForm.intTwoCuspReduce M H p ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩ with hx₀def
  have hx0 : ω = Φ x₀ := by
    apply hinj
    rw [hωΘ, hΦΘ]
    exact PoleDescent.intSeriesC_eq_of_intTwoCuspReduce_eq K hpM hHp W
      ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩ (yx x₀) (hyx x₀).symm pf (pfx x₀) hpf (hpfx' x₀)
  rw [ModularCurve.mem_ssPolarDifferentials_iff]
  intro v
  refine ⟨fun hv => hωreg v hv, fun hv => ?_⟩
  rw [hx0]
  exact (hfinal _ v hv).hasSimplePoleAt

end S_CuspForm_exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet
end P2MW
export P2MW.S_CuspForm_exists_mem_ssPolarDifferentials_diffQExp_eq_intSeriesC_of_mem_twoCuspIntegralSet (solution)

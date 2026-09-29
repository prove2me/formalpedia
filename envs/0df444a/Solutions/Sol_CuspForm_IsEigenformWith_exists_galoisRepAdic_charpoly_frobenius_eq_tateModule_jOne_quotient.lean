-- Prove2me | solution 1 for CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_tateModule_jOne_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1567a2fb-81f6-58d7-9e76-be2f99ad7a0c

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1HeckeModule
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Theorems.Thm_ModularCurve_heckeDiamondCommuteBar
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import Theorems.Thm_CuspForm_IsEigenformWith_exists_ringHom_rationalHeckeAlgebraOne_mul_eq
import Theorems.Thm_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar_tateModule_quotient
import Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_tateModule_jOne_quotient
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime CuspForm.GammaH_finiteIndex CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par Ihara.instGroupIharaAmalgam CohCarrier.GammaHLower_finiteIndex ValuationSubring.instIsAlgClosedResidueField ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero"
p2m_attr_erase "simp" "CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply CohCarrier.jConjGammaH_jConjGammaH CohCarrier.coe_jConjGammaH CohCarrier.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one"
p2m_attr_erase "simp" "HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway CuspForm.PeterssonCoset.mapGL_apply CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.coe_uElt CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.coe_laurentReductionDegZero ModularCurve.laurentReductionDiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

open Polynomial
open scoped TensorProduct

noncomputable section

namespace E1G1X

theorem padicIntToRing_injective (p : ℕ) [Fact p.Prime] (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (hp : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    Function.Injective (GaloisRep.padicIntToRing 𝒪 p hp) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hne
  have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (GaloisRep.padicIntToRing 𝒪 p hp) := by
    rw [hn]; exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_ne_zero n (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hmem

theorem coefficientRing (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪]
    (L' : Type) [Field L'] [Algebra 𝒪 L'] [Algebra (FractionRing 𝒪) L']
    [IsScalarTower 𝒪 (FractionRing 𝒪) L'] [FiniteDimensional (FractionRing 𝒪) L'] :
    ∃ (_ : IsDiscreteValuationRing ↥(integralClosure 𝒪 L')),
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(integralClosure 𝒪 L')) ↥(integralClosure 𝒪 L') ∧
      Finite (IsLocalRing.ResidueField ↥(integralClosure 𝒪 L')) ∧
      CharZero ↥(integralClosure 𝒪 L') ∧
      Module.Finite 𝒪 ↥(integralClosure 𝒪 L') ∧
      IsLocalHom (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) ∧
      Function.Injective (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) ∧
      IsFractionRing ↥(integralClosure 𝒪 L') L' := by
  haveI : Algebra.IsSeparable (FractionRing 𝒪) L' := inferInstance
  obtain ⟨hfin, hdvr, hcomp⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪
      (FractionRing 𝒪) L'
  haveI := hfin
  haveI := hdvr
  have hinjL : Function.Injective (algebraMap 𝒪 L') := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (FractionRing 𝒪) L']
    exact (algebraMap (FractionRing 𝒪) L').injective.comp (IsFractionRing.injective 𝒪 _)
  have hinj : Function.Injective (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) := fun x y h =>
    hinjL (by
      have h' := congrArg (fun z : ↥(integralClosure 𝒪 L') => (z : L')) h
      simpa only [Subalgebra.coe_algebraMap] using h')
  haveI : FaithfulSMul 𝒪 ↥(integralClosure 𝒪 L') :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 _).2 hinj
  have hloc : IsLocalHom (algebraMap 𝒪 ↥(integralClosure 𝒪 L')) :=
    Algebra.IsIntegral.isLocalHom 𝒪 _
  haveI := hloc
  have hres : Finite (IsLocalRing.ResidueField ↥(integralClosure 𝒪 L')) :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) inferInstance
  haveI : CharZero L' :=
    (RingHom.charZero_iff (algebraMap (FractionRing 𝒪) L').injective).1 inferInstance
  have hcz : CharZero ↥(integralClosure 𝒪 L') := (algebraMap ↥(integralClosure 𝒪 L') L').charZero
  have hfrac : IsFractionRing ↥(integralClosure 𝒪 L') L' :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing 𝒪) L'
  exact ⟨hdvr, hcomp, hres, hcz, hfin, hloc, hinj, hfrac⟩

theorem exists_pow_eq_one {M : ℕ} [NeZero M] (ε : DirichletCharacter ℂ M)
    {R : Type} [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : R) (hx : toC x = ε (ℓ : ZMod M)) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_prime_iff_not_dvd hℓ).2 hℓM
  refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, htoC ?_⟩
  rw [map_pow, hx, map_one, ← hu, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one,
    Units.val_one, map_one]

theorem isUnit_map_of_pow_eq_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {x : R} {n : ℕ}
    (hn : 0 < n) (hx : x ^ n = 1) : IsUnit (f x) := by
  have : (f x) ^ n = 1 := by rw [← map_pow, hx, map_one]
  exact IsUnit.of_pow_eq_one this (Nat.pos_iff_ne_zero.1 hn)

section Instances

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]

scoped instance isMulCommutative_A : IsMulCommutative (ModularCurve.rationalHeckeAlgebraOne p J) :=
  Algebra.isMulCommutative_adjoin ℚ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingA : CommRing (ModularCurve.rationalHeckeAlgebraOne p J) := inferInstance

end Instances

set_option maxHeartbeats 64000000 in

theorem main
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ) (hlamS : lam ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsDiscreteValuationRing O'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O'') O'')
        (_ : Finite (IsLocalRing.ResidueField O'')) (_ : CharZero O'')
        (_ : Algebra O' O'') (_ : Module.Finite O' O'') (_ : IsLocalHom (algebraMap O' O'')),
      Function.Injective (algebraMap O' O'') ∧
      ∃ ρ : GaloisRepAdic O'',
        (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap O' O'' (φ (b ℓ))) * X
                  + C (algebraMap O' O'' (φ (e ℓ) * (ℓ : O')))) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ lam → ρ.IsUnramifiedAt ℓ) ∧
        ∃ (_ : Algebra ℤ_[lam] O'') (K₀ : Type) (_ : Field K₀) (_ : Algebra O'' K₀)
          (_ : IsFractionRing O'' K₀) (_ : Algebra ℤ_[lam] K₀) (_ : IsScalarTower ℤ_[lam] O'' K₀)
          (π : K₀ ⊗[ℤ_[lam]] TateModule lam (ModularCurve.JOne M) →ₗ[K₀] K₀ ⊗[O''] ρ.V),
          Function.Surjective π ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (x : K₀ ⊗[ℤ_[lam]] TateModule lam (ModularCurve.JOne M)),
            π ((TateModule.rep lam (ModularCurve.JOne M)
                (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K₀ x) =
              (ρ.ρ σ).baseChange K₀ (π x) := by
  letI := ModularCurve.heckeModuleOneBar M
  have hin : ModularCurve.HeckeDiamondInputsAll M := ModularCurve.heckeDiamondInputsAll M
  have hcomm : ModularCurve.HeckeDiamondCommuteBar M := ModularCurve.heckeDiamondCommuteBar M

  set i𝒪 : ℤ_[lam] →+* O' := GaloisRep.padicIntToRing O' lam hlamO' with hi𝒪
  have hi_inj : Function.Injective i𝒪 := E1G1X.padicIntToRing_injective lam O' hlamO'
  have hg_inj : Function.Injective ((algebraMap O' (FractionRing O')).comp i𝒪) :=
    (IsFractionRing.injective O' (FractionRing O')).comp hi_inj
  set jL : ℚ_[lam] →+* FractionRing O' := IsFractionRing.lift hg_inj with hjL
  have hjL : ∀ c : ℤ_[lam], jL (c : ℚ_[lam]) = algebraMap O' (FractionRing O') (i𝒪 c) := fun c => by
    rw [← PadicInt.algebraMap_apply, hjL, IsFractionRing.lift_algebraMap]
    rfl
  letI : Algebra ℚ_[lam] (AlgebraicClosure (FractionRing O')) :=
    ((algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))).comp jL).toAlgebra
  have halg : ∀ c : ℚ_[lam], algebraMap ℚ_[lam] (AlgebraicClosure (FractionRing O')) c
      = algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O')) (jL c) := fun _ => rfl

  set ψ : R →+* AlgebraicClosure (FractionRing O') :=
    (algebraMap O' (AlgebraicClosure (FractionRing O'))).comp φ with hψ
  obtain ⟨Λ, hc, hT⟩ := hh.exists_ringHom_rationalHeckeAlgebraOne_mul_eq lam hin hcomm
    (↑S : Set ℕ) (AlgebraicClosure (FractionRing O')) R toC htoC ψ b e
    (fun ℓ hℓ hℓM hℓS => hb ℓ hℓ hℓM (fun h' => hℓS (Finset.mem_coe.2 h')))
    (fun ℓ hℓ hℓM hℓS => he ℓ hℓ hℓM (fun h' => hℓS (Finset.mem_coe.2 h')))

  haveI : Module.Finite ℤ_[lam] (TateModule lam (ModularCurve.JOne M)) :=
    ModularCurve.moduleFinite_padicInt_tateModule_jOne M lam
  haveI : Module.Finite ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JOne M)) :=
    inferInstance
  haveI : Module.Finite ℚ_[lam]
      (Module.End ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JOne M))) := inferInstance
  haveI : Module.Finite ℚ_[lam] ↥(ModularCurve.rationalHeckeAlgebraOne lam (ModularCurve.JOne M)) :=
    Module.Finite.of_injective (Subalgebra.val _).toLinearMap Subtype.val_injective
  obtain ⟨L', hL'⟩ : ∃ L' : IntermediateField (FractionRing O') (AlgebraicClosure (FractionRing O')),
      L' = IntermediateField.adjoin (FractionRing O') (Set.range Λ) := ⟨_, rfl⟩
  haveI : FiniteDimensional (FractionRing O') ↥L' := by
    rw [hL']
    exact RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range (R := ℚ_[lam]) Λ
      (fun r => ⟨jL r, by rw [hc r, halg]⟩)
  have hΛmem : ∀ x, Λ x ∈ L' := fun x => by
    rw [hL']
    exact IntermediateField.subset_adjoin (FractionRing O') _ (Set.mem_range_self x)

  obtain ⟨hdvr, hcomp, hres, hcz, hfin, hloc, hinj, hfrac⟩ := E1G1X.coefficientRing O' ↥L'
  haveI := hdvr
  haveI := hfrac
  haveI := hloc
  have hp'' : (lam : ↥(integralClosure O' ↥L')) ∈
      IsLocalRing.maximalIdeal ↥(integralClosure O' ↥L') := by
    rw [IsLocalRing.mem_maximalIdeal, ← map_natCast (algebraMap O' ↥(integralClosure O' ↥L')) lam,
      map_mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact hlamO'

  letI instZpO'' : Algebra ℤ_[lam] ↥(integralClosure O' ↥L') :=
    ((algebraMap O' ↥(integralClosure O' ↥L')).comp i𝒪).toAlgebra
  letI instZpL' : Algebra ℤ_[lam] ↥L' :=
    ((algebraMap ↥(integralClosure O' ↥L') ↥L').comp
      (algebraMap ℤ_[lam] ↥(integralClosure O' ↥L'))).toAlgebra
  haveI instTower : IsScalarTower ℤ_[lam] ↥(integralClosure O' ↥L') ↥L' :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let Λ' : ↥(ModularCurve.rationalHeckeAlgebraOne lam (ModularCurve.JOne M)) →+* ↥L' :=
    { toFun := fun x => ⟨Λ x, hΛmem x⟩
      map_one' := Subtype.ext (map_one Λ)
      map_mul' := fun x y => Subtype.ext (map_mul Λ x y)
      map_zero' := Subtype.ext (map_zero Λ)
      map_add' := fun x y => Subtype.ext (map_add Λ x y) }
  have hΛ'val : ∀ x, ((Λ' x : ↥L') : AlgebraicClosure (FractionRing O')) = Λ x := fun _ => rfl
  have hcoe𝒪 : ∀ y : O',
      ((algebraMap ↥(integralClosure O' ↥L') ↥L' (algebraMap O' ↥(integralClosure O' ↥L') y) : ↥L') :
        AlgebraicClosure (FractionRing O'))
        = algebraMap (FractionRing O') (AlgebraicClosure (FractionRing O'))
            (algebraMap O' (FractionRing O') y) := fun y => by
    rw [← IsScalarTower.algebraMap_apply O' ↥(integralClosure O' ↥L') ↥L']
    change algebraMap O' (AlgebraicClosure (FractionRing O')) y = _
    exact IsScalarTower.algebraMap_apply O' (FractionRing O') _ y
  have hcoe𝒪' : ∀ y : O',
      ((algebraMap ↥(integralClosure O' ↥L') ↥L' (algebraMap O' ↥(integralClosure O' ↥L') y) : ↥L') :
        AlgebraicClosure (FractionRing O'))
        = algebraMap O' (AlgebraicClosure (FractionRing O')) y := fun y => by
    rw [hcoe𝒪]
    exact (IsScalarTower.algebraMap_apply O' (FractionRing O') _ y).symm
  have hΛ'c0 : ∀ c : ℤ_[lam],
      Λ' (algebraMap ℚ_[lam] ↥(ModularCurve.rationalHeckeAlgebraOne lam (ModularCurve.JOne M)) (c : ℚ_[lam]))
        = algebraMap ↥(integralClosure O' ↥L') ↥L'
            (((algebraMap O' ↥(integralClosure O' ↥L')).comp i𝒪) c) := fun c => by
    apply Subtype.ext
    rw [hΛ'val, hc, halg, hjL, RingHom.comp_apply, hcoe𝒪]
  have hΛ'c : ∀ c : ℤ_[lam],
      Λ' (algebraMap ℚ_[lam] ↥(ModularCurve.rationalHeckeAlgebraOne lam (ModularCurve.JOne M)) (c : ℚ_[lam]))
        = algebraMap ℤ_[lam] ↥L' c := fun c => by
    rw [hΛ'c0, IsScalarTower.algebraMap_apply ℤ_[lam] ↥(integralClosure O' ↥L') ↥L' c]
    rfl

  have E1 :=
    ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar_tateModule_quotient M lam
      ↥(integralClosure O' ↥L') ↥L' hp''
  obtain ⟨ρ, hchar, hunr, π, hπ, hπρ, -⟩ := E1 Λ' hΛ'c

  have hp : lam.Prime := Fact.out
  have hMp : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ lam → ¬ ℓ ∣ M * lam := fun ℓ hℓ hℓM hℓp h' =>
    (hℓ.dvd_mul.1 h').elim hℓM (fun h'' => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h''))

  have hunits : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → IsUnit (φ (e ℓ)) := by
    intro ℓ hℓ hℓM hℓS
    obtain ⟨n, hn, hpow⟩ := E1G1X.exists_pow_eq_one ε toC htoC hℓ hℓM (e ℓ) (he ℓ hℓ hℓM hℓS)
    exact E1G1X.isUnit_map_of_pow_eq_one φ hn hpow
  refine ⟨↥(integralClosure O' ↥L'), inferInstance, inferInstance, hdvr, hcomp, hres, hcz,
    inferInstance, hfin, hloc, hinj, ρ, ?_, fun q hq hqM hqp => hunr q hq (hMp q hq hqM hqp),
    instZpO'', ↥L', inferInstance, inferInstance, hfrac, instZpL', instTower, π, hπ, hπρ⟩
  intro ℓ hℓ hℓM hℓS A hA σ hσ
  have hℓp : ℓ ≠ lam := fun h' => hℓS (by rw [h']; exact hlamS)
  have hℓS' : ℓ ∉ (↑S : Set ℕ) := fun h' => hℓS (Finset.mem_coe.1 h')
  have hT' := hT ℓ hℓ hℓM hℓS'
  have hTℓ := hT'.1
  have hDℓ := hT'.2
  have hu := hunits ℓ hℓ hℓM hℓS

  have hψe : ψ (e ℓ) = algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (e ℓ)) := rfl
  have hψb : ψ (b ℓ) = algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (b ℓ)) := rfl
  have hd' : Λ' (ModularCurve.rationalDiamondOne lam (ModularCurve.JOne M) ℓ)
      * algebraMap ↥(integralClosure O' ↥L') ↥L'
          (algebraMap O' ↥(integralClosure O' ↥L') (φ (e ℓ))) = 1 := by
    apply (algebraMap ↥L' (AlgebraicClosure (FractionRing O'))).injective
    rw [map_mul, map_one, IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
      hΛ'val, hcoe𝒪', ← hψe]
    exact hDℓ
  have hunit : algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (e ℓ))
      * algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O') = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have hΛT : Λ (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
      = algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O')
          * algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (b ℓ)) := by
    calc Λ (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
        = Λ (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
            * (algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (e ℓ))
              * algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O')) := by
          rw [hunit, mul_one]
      _ = (Λ (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) * ψ (e ℓ))
            * algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O') := by
          rw [hψe, mul_assoc]
      _ = algebraMap O' (AlgebraicClosure (FractionRing O')) ((hu.unit⁻¹ : O'ˣ) : O')
            * algebraMap O' (AlgebraicClosure (FractionRing O')) (φ (b ℓ)) := by
          rw [hTℓ, hψb, mul_comm]
  have ha' : Λ' (ModularCurve.rationalHeckeOne lam (ModularCurve.JOne M) ⟨ℓ, hℓ⟩)
      = algebraMap ↥(integralClosure O' ↥L') ↥L'
          (algebraMap O' ↥(integralClosure O' ↥L') (((hu.unit⁻¹ : O'ˣ) : O') * φ (b ℓ))) := by
    apply Subtype.ext
    rw [hΛ'val, hcoe𝒪', map_mul]
    exact hΛT
  have hmain := hchar ℓ hℓ (hMp ℓ hℓ hℓM hℓp) _ _ ha' hd' A hA σ hσ
  rw [hmain]
  have hda : algebraMap O' ↥(integralClosure O' ↥L') (φ (e ℓ))
        * algebraMap O' ↥(integralClosure O' ↥L') (((hu.unit⁻¹ : O'ˣ) : O') * φ (b ℓ))
      = algebraMap O' ↥(integralClosure O' ↥L') (φ (b ℓ)) := by
    rw [← map_mul, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hdℓ : algebraMap O' ↥(integralClosure O' ↥L') (φ (e ℓ)) * (ℓ : ↥(integralClosure O' ↥L'))
      = algebraMap O' ↥(integralClosure O' ↥L') (φ (e ℓ) * (ℓ : O')) := by
    rw [map_mul, map_natCast]
  rw [hda, hdℓ]

end E1G1X

theorem solution
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsEigenformWith ε h)
    (lam : ℕ) [Fact lam.Prime] (S : Finset ℕ) (hlamS : lam ∈ S)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (R : Type) [CommRing R] (toC : R →+* ℂ) (htoC : Function.Injective toC) (φ : R →+* O')
    (b e : ℕ → R)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (b ℓ) = ModularFormClass.qCoeff h ℓ)
    (he : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S → toC (e ℓ) = ε (ℓ : ZMod M)) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsDiscreteValuationRing O'')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal O'') O'')
        (_ : Finite (IsLocalRing.ResidueField O'')) (_ : CharZero O'')
        (_ : Algebra O' O'') (_ : Module.Finite O' O'') (_ : IsLocalHom (algebraMap O' O'')),
      Function.Injective (algebraMap O' O'') ∧
      ∃ ρ : GaloisRepAdic O'',

        (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ M → ℓ ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) =
                X ^ 2 - C (algebraMap O' O'' (φ (b ℓ))) * X
                  + C (algebraMap O' O'' (φ (e ℓ) * (ℓ : O')))) ∧

        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ lam → ρ.IsUnramifiedAt ℓ) ∧

        ∃ (_ : Algebra ℤ_[lam] O'') (K₀ : Type) (_ : Field K₀) (_ : Algebra O'' K₀)
          (_ : IsFractionRing O'' K₀) (_ : Algebra ℤ_[lam] K₀) (_ : IsScalarTower ℤ_[lam] O'' K₀)
          (π : K₀ ⊗[ℤ_[lam]] TateModule lam (ModularCurve.JOne M) →ₗ[K₀] K₀ ⊗[O''] ρ.V),
          Function.Surjective π ∧
          ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
            (x : K₀ ⊗[ℤ_[lam]] TateModule lam (ModularCurve.JOne M)),
            π ((TateModule.rep lam (ModularCurve.JOne M)
                (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K₀ x) =
              (ρ.ρ σ).baseChange K₀ (π x) :=
  E1G1X.main hh lam S hlamS O' hlamO' R toC htoC φ b e hb he

end
end S_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_tateModule_jOne_quotient
end P2MW
export P2MW.S_CuspForm_IsEigenformWith_exists_galoisRepAdic_charpoly_frobenius_eq_tateModule_jOne_quotient (solution)

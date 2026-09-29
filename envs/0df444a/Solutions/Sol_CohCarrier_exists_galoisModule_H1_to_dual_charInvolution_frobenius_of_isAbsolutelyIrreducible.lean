-- Prove2me | solution 1 for CohCarrier.exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a028e400-edd9-53b4-bc1f-228b221177a2

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_charInvolution_comp_opFamily
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
import Theorems.Thm_CohCarrier_exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius
import Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_trace_frobenius_ne_of_isAbsolutelyIrreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions"
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.JH.torsionGaloisRep_apply ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply ModularCurve.coe_laurentReductionDegZero ModularCurve.laurentReductionDiv_apply ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "Gen heckeTL heckeTL_apply diamondL opFamily Gen.T Gen.dia GammaH H1 conjUpperMat GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conjHom diamondRaw charInvolution charInvolution_comp_opFamily heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius"
namespace ESFibre
p2m_open "CohCarrier"

section Stable

variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]

theorem heckeT_apply_eq_sum (φ : H1 M Hs A) (u : ↥(GammaH M Hs))
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)))] :
    heckeT M Hs ℓ A φ (Additive.ofMul u) =
      ∑ O : Quotient (MulAction.orbitRel (Subgroup.zpowers u)
          (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)),
        φ (Additive.ofMul (conjL M Hs ℓ
          ⟨O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out⟩)) := by
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M Hs ℓ)) u) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  rfl

theorem trace_conjUpperMat (X : SL(2, ℤ)) (hX : (ℓ : ℤ) ∣ X 0 1) :
    ((conjUpperMat ℓ X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((X : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [conjUpperMat]

theorem trace_sq_conj_pow (γ r : SL(2, ℤ)) (m : ℕ)
    (hγ : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    (((r⁻¹ * γ ^ m * r : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4 := by
  obtain ⟨ε, δ, h, hε, rfl⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four γ hγ
  have hu : ∀ n : ℕ, ((r⁻¹ * (δ * ModularGroup.T ^ h * δ⁻¹) ^ n * r : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    intro n
    rw [conj_pow, ← zpow_natCast, ← _root_.zpow_mul,
      show r⁻¹ * (δ * ModularGroup.T ^ (h * (n : ℤ)) * δ⁻¹) * r =
        (r⁻¹ * δ) * (ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹) by group,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      show ModularGroup.T ^ (h * (n : ℤ)) * (r⁻¹ * δ)⁻¹ * (r⁻¹ * δ) = ModularGroup.T ^ (h * (n : ℤ)) by group,
      ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
    ring
  rcases hε with rfl | rfl
  · rw [one_mul, hu]; norm_num
  · rw [neg_one_mul, neg_pow]
    rcases neg_one_pow_eq_or SL(2, ℤ) m with h1 | h1
    · rw [h1, one_mul, hu]; norm_num
    · rw [h1, neg_one_mul, mul_neg, neg_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
        neg_sq, hu]
      norm_num

theorem heckeT_isParabolicHom (φ : H1 M Hs A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (heckeT M Hs ℓ A φ) := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers γ)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ))) := Fintype.ofFinite _
  rw [heckeT_apply_eq_sum]
  refine Finset.sum_eq_zero fun O _ => hφ _ ?_
  set x : ↥(GammaHUpper M Hs ℓ) := ⟨O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem _ γ O.out⟩ with hxdef
  have hx : ((conjL M Hs ℓ x : ↥(GammaH M Hs)) : SL(2, ℤ)) =
      conjUpperMat ℓ ((x : ↥(GammaH M Hs)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper M Hs ℓ x) := rfl
  rw [hx, trace_conjUpperMat, hxdef]
  show ((((O.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) O.out * O.out.out : ↥(GammaH M Hs)) :
    SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  exact trace_sq_conj_pow _ _ _ hγ

theorem diamondRaw_isParabolicHom (σ : Gamma0 M) (φ : H1 M Hs A)
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (diamondRaw M Hs A σ φ) := by
  intro γ hγ
  show φ (Additive.ofMul (conjHom M Hs σ γ)) = 0
  refine hφ _ ?_
  show ((((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
    show (σ : SL(2, ℤ))⁻¹ * ((σ : SL(2, ℤ)) * (γ : SL(2, ℤ))) = γ by group]
  exact hγ

end Stable

section OpStable

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]

abbrev Par : Submodule 𝒪 (H1 M H 𝒪) := ModularCurve.Period.parabolicHoms 𝒪 (GammaH M H) 𝒪

theorem opFamily_mem_Par (g : Gen M S) (v : H1 M H 𝒪) (hv : v ∈ Par M H 𝒪) :
    opFamily M H S 𝒪 g v ∈ Par M H 𝒪 := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff] at hv ⊢
  cases g with
  | T ℓ hℓ hℓS hℓM =>
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    show ModularCurve.Period.IsParabolicHom _ (heckeTL M H 𝒪 ℓ v)
    rw [heckeTL_apply]
    exact heckeT_isParabolicHom M H ℓ v hv
  | U q hq hqM =>
    haveI : NeZero q := ⟨hq.ne_zero⟩
    show ModularCurve.Period.IsParabolicHom _ (heckeTL M H 𝒪 q v)
    rw [heckeTL_apply]
    exact heckeT_isParabolicHom M H q v hv
  | dia d =>
    show ModularCurve.Period.IsParabolicHom _ (diamondL M H 𝒪 d v)
    exact diamondRaw_isParabolicHom M H _ v hv

end OpStable

section Eigen

variable {k : Type} [Field k]
variable {V : Type} [AddCommGroup V] [Module k V]
variable {G : Type} (t : G → Module.End k V) (c : G → k)

def eig : Submodule k V where
  carrier := {w | ∀ g, t g w = c g • w}
  zero_mem' g := by rw [map_zero, smul_zero]
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g, smul_add]
  smul_mem' a {x} hx g := by rw [map_smul, hx g, smul_comm]

theorem mem_eig {w : V} : w ∈ eig t c ↔ ∀ g, t g w = c g • w := Iff.rfl

variable {Γ : Type} [Group Γ] (σ : Γ →* Module.End k V)

theorem apply_mem_eig (f : Module.End k V) (hf : ∀ g, t g * f = f * t g) {w : V} (hw : w ∈ eig t c) :
    f w ∈ eig t c := by
  intro g
  have := congrArg (fun h : Module.End k V => h w) (hf g)
  simp only [Module.End.mul_apply] at this
  rw [this, hw g, map_smul]

variable (hcomm : ∀ (g : G) (τ : Γ), t g * σ τ = σ τ * t g)

def sigmaW : Γ →* Module.End k ↥(eig t c) where
  toFun τ := (σ τ).restrict fun w hw => apply_mem_eig t c (σ τ) (fun g => hcomm g τ) hw
  map_one' := by
    ext w
    simp
  map_mul' τ₁ τ₂ := by
    ext w
    simp

@[scoped simp] theorem coe_sigmaW_apply (τ : Γ) (w : ↥(eig t c)) :
    ((sigmaW t c σ hcomm τ w : ↥(eig t c)) : V) = σ τ (w : V) := rfl

theorem ker_le_ker_sigmaW : σ.ker ≤ (sigmaW t c σ hcomm).ker := by
  intro τ hτ
  rw [MonoidHom.mem_ker] at hτ ⊢
  ext w
  rw [coe_sigmaW_apply, hτ]
  rfl

end Eigen

section Fibre

variable {𝒪 : Type} [CommRing 𝒪]
variable {k : Type} [Field k] [Algebra 𝒪 k]
variable {Λ : Type} [AddCommGroup Λ] [Module 𝒪 Λ]
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 Λ] [IsScalarTower 𝒪 𝕋 Λ]
variable (par : Submodule 𝒪 Λ)
variable {G : Type} (op : G → 𝕋)
variable (θ : 𝕋 →ₐ[𝒪] k) (c : G → k)
variable {V : Type} [AddCommGroup V] [Module k V]
variable (t : G → Module.End k V) (Φ : Λ →ₗ[𝒪] Module.Dual k V)

def goodSubalg
    : Subalgebra 𝒪 𝕋 where
  carrier := {s | (∀ v ∈ par, s • v ∈ par) ∧
    ∀ u ∈ par, (eig t c).dualRestrict (Φ (s • u)) = θ s • (eig t c).dualRestrict (Φ u)}
  mul_mem' {a b} ha hb := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [mul_smul]; exact ha.1 _ (hb.1 v hv)
    · rw [mul_smul, ha.2 _ (hb.1 u hu), hb.2 u hu, map_mul, mul_smul]
  one_mem' := ⟨fun v hv => by rwa [one_smul], fun u hu => by rw [one_smul, map_one, one_smul]⟩
  add_mem' {a b} ha hb := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [add_smul]; exact par.add_mem (ha.1 v hv) (hb.1 v hv)
    · rw [add_smul, map_add, map_add, ha.2 u hu, hb.2 u hu, map_add, add_smul]
  zero_mem' := ⟨fun v hv => by rw [zero_smul]; exact par.zero_mem,
    fun u hu => by rw [zero_smul, map_zero, map_zero, map_zero, zero_smul]⟩
  algebraMap_mem' r := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [algebraMap_smul]; exact par.smul_mem r hv
    · rw [algebraMap_smul, map_smul, AlgHom.commutes, LinearMap.map_smul_of_tower, algebraMap_smul]

variable (hop_st : ∀ (g : G) (v : Λ), v ∈ par → op g • v ∈ par)
variable (hθ : ∀ g, θ (op g) = c g)
variable (hΦop : ∀ (g : G) (v : Λ), v ∈ par → Φ (op g • v) = (Φ v) ∘ₗ t g)
variable (hgen : Algebra.adjoin 𝒪 (Set.range op) = ⊤)

include hop_st hθ hΦop in
theorem op_mem_goodSubalg (g : G) : op g ∈ goodSubalg par θ c t Φ := by
  refine ⟨fun v hv => hop_st g v hv, fun u hu => ?_⟩
  rw [hΦop g u hu, hθ]
  ext w
  rw [Submodule.dualRestrict_apply, LinearMap.smul_apply, Submodule.dualRestrict_apply,
    LinearMap.comp_apply, (mem_eig t c).mp w.2 g, map_smul]

include hop_st hθ hΦop hgen in
theorem goodSubalg_eq_top : goodSubalg par θ c t Φ = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← hgen]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨g, rfl⟩
  exact op_mem_goodSubalg par op θ c t Φ hop_st hθ hΦop g

include hop_st hθ hΦop hgen in

theorem smul_mem_par (s : 𝕋) (v : Λ) (hv : v ∈ par) : s • v ∈ par :=
  ((goodSubalg_eq_top par op θ c t Φ hop_st hθ hΦop hgen).symm ▸ (Algebra.mem_top : s ∈ _)).1 v hv

include hop_st hθ hΦop hgen in

theorem dualRestrict_smul (s : 𝕋) (u : Λ) (hu : u ∈ par) :
    (eig t c).dualRestrict (Φ (s • u)) = θ s • (eig t c).dualRestrict (Φ u) :=
  ((goodSubalg_eq_top par op θ c t Φ hop_st hθ hΦop hgen).symm ▸ (Algebra.mem_top : s ∈ _)).2 u hu

def mPar : Submodule 𝒪 Λ :=
  Submodule.span 𝒪 {x | ∃ s : 𝕋, θ s = 0 ∧ ∃ w ∈ par, x = s • w}

variable (hk : Function.Surjective (algebraMap 𝒪 k))
variable (hΦsurj : par.map Φ = ⊤)

include hop_st hθ hΦop hgen hk hΦsurj in

theorem dualCoannihilator_le :
    (Submodule.span k ((fun x => Φ x) '' (mPar par θ : Set Λ))).dualCoannihilator ≤ eig t c := by
  intro v hv g
  rw [Submodule.mem_dualCoannihilator] at hv
  obtain ⟨r, hr⟩ := hk (c g)

  have hs : θ (op g - algebraMap 𝒪 𝕋 r) = 0 := by rw [map_sub, hθ, AlgHom.commutes, hr, sub_self]
  have key : ∀ u ∈ par, Φ u (t g v - c g • v) = 0 := by
    intro u hu
    have hmem : Φ ((op g - algebraMap 𝒪 𝕋 r) • u) ∈
        Submodule.span k ((fun x => Φ x) '' (mPar par θ : Set Λ)) :=
      Submodule.subset_span ⟨_, Submodule.subset_span ⟨_, hs, u, hu, rfl⟩, rfl⟩
    have h0 := hv _ hmem
    rw [sub_smul, map_sub, hΦop g u hu, algebraMap_smul, map_smul, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, ← algebraMap_smul k r ((Φ u) v), hr] at h0
    rw [map_sub, map_smul]
    exact h0

  have hall : ∀ f : Module.Dual k V, f (t g v - c g • v) = 0 := by
    intro f
    have hf : f ∈ par.map Φ := by rw [hΦsurj]; exact Submodule.mem_top
    obtain ⟨u, hu, rfl⟩ := hf
    exact key u hu
  have := (Module.forall_dual_apply_eq_zero_iff k (t g v - c g • v)).mp hall
  exact sub_eq_zero.mp this

variable [FiniteDimensional k V]

include hop_st hθ hΦop hgen hk hΦsurj in

theorem dualAnnihilator_le :
    (eig t c).dualAnnihilator ≤ Submodule.span k ((fun x => Φ x) '' (mPar par θ : Set Λ)) := by
  calc (eig t c).dualAnnihilator
      ≤ (Submodule.span k ((fun x => Φ x) '' (mPar par θ : Set Λ))).dualCoannihilator.dualAnnihilator :=
        Submodule.dualAnnihilator_anti
          (dualCoannihilator_le par op θ c t Φ hop_st hθ hΦop hgen hk hΦsurj)
    _ = _ := Subspace.dualCoannihilator_dualAnnihilator_eq

include hop_st hθ hΦop hgen hk in

theorem exists_of_mem_span (f : Module.Dual k V)
    (hf : f ∈ Submodule.span k ((fun x => Φ x) '' (mPar par θ : Set Λ))) :
    ∃ y ∈ mPar par θ, y ∈ par ∧ Φ y = f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, hy, ?_, rfl⟩

    refine Submodule.span_induction (p := fun z _ => z ∈ par) ?_ par.zero_mem
      (fun _ _ _ _ ha hb => par.add_mem ha hb) (fun r _ _ ha => par.smul_mem r ha) hy
    rintro _ ⟨s, hs, w, hw, rfl⟩
    exact smul_mem_par par op θ c t Φ hop_st hθ hΦop hgen s w hw
  | zero => exact ⟨0, Submodule.zero_mem _, par.zero_mem, map_zero Φ⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha', rfl⟩ := hx
    obtain ⟨b, hb, hb', rfl⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, par.add_mem ha' hb', map_add Φ a b⟩
  | smul a x _ hx =>
    obtain ⟨y, hy, hy', rfl⟩ := hx
    obtain ⟨r, rfl⟩ := hk a
    exact ⟨r • y, Submodule.smul_mem _ r hy, par.smul_mem r hy', by rw [map_smul, algebraMap_smul]⟩

variable [IsLocalRing 𝒪]
variable (hΦker : ∀ v : Λ, v ∈ par → (Φ v = 0 ↔ v ∈ IsLocalRing.maximalIdeal 𝒪 • par))

include hk in

theorem algebraMap_eq_zero_of_mem {r : 𝒪} (hr : r ∈ IsLocalRing.maximalIdeal 𝒪) :
    algebraMap 𝒪 k r = 0 := by
  have hmax : (RingHom.ker (algebraMap 𝒪 k)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hk
  have heq := IsLocalRing.eq_maximalIdeal hmax
  rw [← heq] at hr
  exact hr

include hk in
theorem maximalIdeal_smul_le_mPar : IsLocalRing.maximalIdeal 𝒪 • par ≤ mPar par θ := by
  refine Submodule.smul_le.mpr fun r hr w hw => ?_
  refine Submodule.subset_span ⟨algebraMap 𝒪 𝕋 r, ?_, w, hw, (algebraMap_smul 𝕋 r w).symm⟩
  rw [AlgHom.commutes]
  exact algebraMap_eq_zero_of_mem hk hr

include hop_st hθ hΦop hgen hk hΦsurj hΦker in

theorem mem_mPar_of_dualRestrict_eq_zero (u : Λ) (hu : u ∈ par)
    (h0 : (eig t c).dualRestrict (Φ u) = 0) : u ∈ mPar par θ := by
  have hann : Φ u ∈ (eig t c).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    have := congrArg (fun f : Module.Dual k ↥(eig t c) => f ⟨w, hw⟩) h0
    simpa [Submodule.dualRestrict_apply] using this
  obtain ⟨y, hy, hy', hyu⟩ := exists_of_mem_span par op θ c t Φ hop_st hθ hΦop hgen hk (Φ u)
    (dualAnnihilator_le par op θ c t Φ hop_st hθ hΦop hgen hk hΦsurj hann)
  have hdiff : u - y ∈ IsLocalRing.maximalIdeal 𝒪 • par := by
    rw [← hΦker _ (par.sub_mem hu hy'), map_sub, hyu, sub_self]
  have : u = y + (u - y) := by abel
  rw [this]
  exact Submodule.add_mem _ hy (maximalIdeal_smul_le_mPar par θ hk hdiff)

end Fibre

section Corner

variable {𝒪 : Type} [CommRing 𝒪]
variable {k : Type} [Field k] [Algebra 𝒪 k]
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable (Sp : IharaLemma.IdempotentSplitting 𝕋) (i : Fin Sp.n) (πk : Sp.CornerRing i →ₐ[𝒪] k)

def toCornerAlgHom : 𝕋 →ₐ[𝒪] Sp.CornerRing i :=
  { Sp.toCornerRing i with commutes' := fun _ => rfl }

@[scoped simp] theorem toCornerAlgHom_apply (b : 𝕋) : toCornerAlgHom (𝒪 := 𝒪) Sp i b = Sp.toCornerRing i b := rfl

theorem toCornerRing_coe (z : Sp.CornerRing i) : Sp.toCornerRing i (z : 𝕋) = z := by
  apply IharaLemma.IdempotentSplitting.ext_cornerRing
  rw [IharaLemma.IdempotentSplitting.coe_toCornerRing, Sp.e_mul_coe, Sp.coe_mul_e]

theorem toCornerRing_e : Sp.toCornerRing i (Sp.e i) = 1 := by
  apply IharaLemma.IdempotentSplitting.ext_cornerRing
  rw [IharaLemma.IdempotentSplitting.coe_toCornerRing, IharaLemma.IdempotentSplitting.coe_one_cornerRing,
    (Sp.idem i).eq, (Sp.idem i).eq]

variable (hk : Function.Surjective (algebraMap 𝒪 k))

include hk in
theorem πk_surjective : Function.Surjective πk := fun x => by
  obtain ⟨r, rfl⟩ := hk x
  exact ⟨algebraMap 𝒪 _ r, πk.commutes r⟩

include hk in

theorem mem_maximalIdeal_iff (z : Sp.CornerRing i) :
    z ∈ IsLocalRing.maximalIdeal (Sp.CornerRing i) ↔ πk z = 0 := by
  have hmax : (RingHom.ker (πk : Sp.CornerRing i →+* k)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (πk_surjective Sp i πk hk)
  rw [← IsLocalRing.eq_maximalIdeal hmax, RingHom.mem_ker]
  rfl

include hk in

theorem exists_e_eq_mul (t₀ : 𝕋) (ht₀ : πk (Sp.toCornerRing i t₀) ≠ 0) : ∃ x : 𝕋, Sp.e i = t₀ * x := by
  have hunit : IsUnit (Sp.toCornerRing i t₀) := by
    by_contra h
    exact ht₀ ((mem_maximalIdeal_iff Sp i πk hk _).mp ((IsLocalRing.mem_maximalIdeal _).mpr h))
  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  refine ⟨Sp.e i * (u : 𝕋), ?_⟩
  have h : (Sp.e i * t₀ * Sp.e i) * (u : 𝕋) = Sp.e i := congrArg Subtype.val hu
  calc Sp.e i = (Sp.e i * t₀ * Sp.e i) * (u : 𝕋) := h.symm
    _ = t₀ * (Sp.e i * Sp.e i) * (u : 𝕋) := by ring
    _ = t₀ * (Sp.e i * (u : 𝕋)) := by rw [(Sp.idem i).eq, mul_assoc]

variable {Λ : Type} [AddCommGroup Λ] [Module 𝕋 Λ] [Module 𝒪 Λ] [IsScalarTower 𝒪 𝕋 Λ]

theorem smul_corner_eq (b : 𝕋) (m : ↥(IharaLemma.cornerSubmodule (M := Λ) (Sp.e i))) :
    b • m = Sp.toCornerRing i b • m := by
  apply Subtype.ext
  rw [Submodule.coe_smul, IharaLemma.IdempotentSplitting.coe_cornerSmul,
    IharaLemma.IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul, Sp.e_smul_coe,
    ← Submodule.coe_smul, Sp.e_smul_coe]

include hk in

theorem toCorner_mem_of_mem_mPar (par : Submodule 𝒪 Λ) (x : Λ)
    (hx : x ∈ mPar (𝕋 := 𝕋) par ((πk.comp (toCornerAlgHom Sp i)))) :
    IharaLemma.toCorner (M := Λ) (Sp.e i) x ∈
      IsLocalRing.maximalIdeal (Sp.CornerRing i) •
        (⊤ : Submodule (Sp.CornerRing i) ↥(IharaLemma.cornerSubmodule (M := Λ) (Sp.e i))) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, hs, w, hw, rfl⟩ := hy
    rw [map_smul, smul_corner_eq]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [mem_maximalIdeal_iff Sp i πk hk]
    exact hs
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha =>
    rw [LinearMap.map_smul_of_tower, ← algebraMap_smul (Sp.CornerRing i) r]
    exact Submodule.smul_mem _ _ ha

end Corner

section Involution

variable {𝒪 : Type} [CommRing 𝒪]
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {Λ : Type} [AddCommGroup Λ] [Module 𝕋 Λ] [Module 𝒪 Λ] [IsScalarTower 𝒪 𝕋 Λ]

def commSubalg (ι : Λ →ₗ[𝒪] Λ) : Subalgebra 𝒪 𝕋 where
  carrier := {s | ∀ v : Λ, ι (s • v) = s • ι v}
  mul_mem' {a b} ha hb v := by rw [mul_smul, ha, hb, mul_smul]
  one_mem' v := by rw [one_smul, one_smul]
  add_mem' {a b} ha hb v := by rw [add_smul, map_add, ha, hb, add_smul]
  zero_mem' v := by rw [zero_smul, map_zero, zero_smul]
  algebraMap_mem' r v := by rw [algebraMap_smul, algebraMap_smul, map_smul]

theorem comm_all (ι : Λ →ₗ[𝒪] Λ) {G : Type} (op : G → 𝕋)
    (hgen : Algebra.adjoin 𝒪 (Set.range op) = ⊤)
    (hcomm : ∀ (g : G) (v : Λ), ι (op g • v) = op g • ι v) (s : 𝕋) (v : Λ) :
    ι (s • v) = s • ι v := by
  have hle : Algebra.adjoin 𝒪 (Set.range op) ≤ commSubalg (𝕋 := 𝕋) ι := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨g, rfl⟩
    exact hcomm g
  have hs : s ∈ commSubalg (𝕋 := 𝕋) ι := by
    apply hle
    rw [hgen]
    exact Algebra.mem_top
  exact hs v

end Involution

end CohCarrier.ESFibre
p2m_reactivate "P2MW.S_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible.CohCarrier P2MW.S_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible.CohCarrier.ESFibre"
p2m_reactivate "P2MW.S_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible.CohCarrier"

open _root_.CohCarrier _root_.P2MW.S_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible.CohCarrier CohCarrier.ESFibre in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ) (S : Finset ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 M' H' 𝒪)]
    [IsScalarTower 𝒪 𝕋 (CohCarrier.H1 M' H' 𝒪)]
    (hfaith : ∀ t : 𝕋, (∀ v : CohCarrier.H1 M' H' 𝒪, t • v = 0) → t = 0)
    (op : CohCarrier.Gen M' ↑S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M' ↑S) (v : CohCarrier.H1 M' H' 𝒪),
      op g • v = CohCarrier.opFamily M' H' ↑S 𝒪 g v)
    (hgen : Algebra.adjoin 𝒪 (Set.range op) = ⊤)
    (θbar : CohCarrier.Gen M' ↑S → k)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n) (πk : S'.CornerRing i₀ →ₐ[𝒪] k)
    (hπk : ∀ g : CohCarrier.Gen M' ↑S, πk (S'.toCornerRing i₀ (op g)) = θbar g)
    (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module k W) (_ : FiniteDimensional k W)
      (σW : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (W →ₗ[k] W))
      (Ψ : CohCarrier.H1 M' H' 𝒪 →+ Module.Dual k W),
      IsOpen ((σW.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∧
      (∀ (t : 𝕋) (v : CohCarrier.H1 M' H' 𝒪), Ψ (t • v) = πk (S'.toCornerRing i₀ t) • Ψ v) ∧
      (∀ v : CohCarrier.H1 M' H' 𝒪,
        Ψ (CohCarrier.charInvolution M' H' 𝒪 𝒪 v) = (Ψ v) ∘ₗ σW complexConjugation) ∧
      Function.Surjective Ψ ∧
      (∀ m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
        Ψ (m : CohCarrier.H1 M' H' 𝒪) = 0 ↔
          m ∈ IsLocalRing.maximalIdeal (S'.CornerRing i₀) •
            (⊤ : Submodule (S'.CornerRing i₀)
              ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓM : ¬ ℓ ∣ M'), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            σW σ * σW σ - θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) • σW σ +
              ((ℓ : k) * θbar (CohCarrier.Gen.dia
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))) • 1 = 0) := by
  classical

  set Λ := CohCarrier.H1 M' H' 𝒪
  set par : Submodule 𝒪 (CohCarrier.H1 M' H' 𝒪) :=
    ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' H') 𝒪 with hpar
  set e : 𝕋 := S'.e i₀ with he

  let θ : 𝕋 →ₐ[𝒪] k := πk.comp (toCornerAlgHom S' i₀)
  have hθapp : ∀ s : 𝕋, θ s = πk (S'.toCornerRing i₀ s) := fun s => rfl
  have hθ : ∀ g, θ (op g) = θbar g := fun g => hπk g

  have hop_st : ∀ (g : CohCarrier.Gen M' ↑S) (v : Λ), v ∈ par → op g • v ∈ par := by
    intro g v hv
    rw [hop]
    exact opFamily_mem_Par M' H' ↑S 𝒪 g v hv

  obtain ⟨V, _iV₁, _iV₂, _iV₃, σV, tV, Φ, hopenV, hcommV, hΦop', hΦι, hΦsurj, hΦker, hES⟩ :=
    CohCarrier.exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius
      (𝒪 := 𝒪) hk p M' H' (↑S : Set ℕ)
  have hΦop : ∀ (g : CohCarrier.Gen M' ↑S) (v : Λ), v ∈ par → Φ (op g • v) = (Φ v) ∘ₗ tV g := by
    intro g v hv
    rw [hop]
    exact hΦop' g v hv

  have hst : ∀ (s : 𝕋) (v : Λ), v ∈ par → s • v ∈ par :=
    smul_mem_par par op θ θbar tV Φ hop_st hθ hΦop hgen
  have hfib : ∀ (s : 𝕋) (u : Λ), u ∈ par →
      (eig tV θbar).dualRestrict (Φ (s • u)) = θ s • (eig tV θbar).dualRestrict (Φ u) :=
    dualRestrict_smul par op θ θbar tV Φ hop_st hθ hΦop hgen

  obtain ⟨ℓ₀, A₀, σ₀, hℓ₀, hℓ₀1, hℓ₀S, hA₀, hσ₀, hne⟩ :=
    ResidualGaloisRep.exists_prime_modEq_one_trace_frobenius_ne_of_isAbsolutelyIrreducible
      p hp2 ρbar hirr M' S
  have hℓ₀S' : ℓ₀ ∉ (↑S : Set ℕ) := fun h => hℓ₀S (Finset.mem_coe.mp h)
  have hℓ₀M : ¬ ℓ₀ ∣ M' := by
    intro hdvd
    have h1 : ℓ₀ ∣ 1 := by
      have hmod := (Nat.modEq_iff_dvd' hℓ₀.one_lt.le).mp hℓ₀1.symm
      have : ℓ₀ ∣ ℓ₀ - 1 := dvd_trans hdvd hmod
      have h2 : ℓ₀ ∣ ℓ₀ - (ℓ₀ - 1) := Nat.dvd_sub dvd_rfl this
      rwa [Nat.sub_sub_self hℓ₀.one_lt.le] at h2
    exact hℓ₀.one_lt.ne' (Nat.dvd_one.mp h1)
  have htrace : θbar (CohCarrier.Gen.T ℓ₀ hℓ₀ hℓ₀S' hℓ₀M) ≠ (ℓ₀ : k) + 1 := by
    rw [← hatt ℓ₀ hℓ₀ hℓ₀S' hℓ₀M A₀ hA₀ σ₀ hσ₀]
    exact hne
  set t₀ : 𝕋 := op (CohCarrier.Gen.T ℓ₀ hℓ₀ hℓ₀S' hℓ₀M) - ((ℓ₀ : 𝕋) + 1) with ht₀
  have hθt₀ : θ t₀ ≠ 0 := by
    rw [ht₀, map_sub, hθ, map_add, map_natCast, map_one]
    exact sub_ne_zero.mpr htrace
  have ht₀par : ∀ v : Λ, t₀ • v ∈ par := by
    intro v
    haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩
    have key := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one M' H' 𝒪 v ℓ₀ hℓ₀
      hℓ₀M hℓ₀1
    rw [ModularCurve.Period.mem_parabolicHoms_iff] at key
    have hv : t₀ • v = CohCarrier.heckeT M' H' ℓ₀ 𝒪 v - (ℓ₀ + 1) • v := by
      rw [ht₀, sub_smul, hop, show ((ℓ₀ : 𝕋) + 1) = ((ℓ₀ + 1 : ℕ) : 𝕋) by push_cast; rfl,
        Nat.cast_smul_eq_nsmul]
      rfl
    change t₀ • v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH M' H') 𝒪
    rw [hv, ModularCurve.Period.mem_parabolicHoms_iff]
    exact key

  obtain ⟨x₀, hx₀⟩ := exists_e_eq_mul S' i₀ πk hk t₀ hθt₀
  have hepar : ∀ v : Λ, e • v ∈ par := by
    intro v
    rw [he, hx₀, mul_smul]
    exact ht₀par _

  let Wsub : Submodule k V := eig tV θbar
  let σW : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End k ↥Wsub :=
    sigmaW tV θbar σV hcommV

  let Ψ : Λ →+ Module.Dual k ↥Wsub :=
    { toFun := fun v => Wsub.dualRestrict (Φ (e • v))
      map_zero' := by rw [smul_zero, map_zero, map_zero]
      map_add' := fun v w => by rw [smul_add, map_add, map_add] }
  have hΨapp : ∀ v, Ψ v = Wsub.dualRestrict (Φ (e • v)) := fun v => rfl

  have hsemi : ∀ (s : 𝕋) (v : Λ), Ψ (s • v) = πk (S'.toCornerRing i₀ s) • Ψ v := by
    intro s v
    rw [hΨapp, hΨapp, ← mul_smul, mul_comm, mul_smul, hfib s (e • v) (hepar v), hθapp]

  have hθe : πk (S'.toCornerRing i₀ e) = 1 := by rw [he, toCornerRing_e, map_one]
  refine ⟨↥Wsub, inferInstance, inferInstance, inferInstance, σW, Ψ, ?_, hsemi, ?_, ?_, ?_, ?_⟩
  ·
    exact Subgroup.isOpen_mono (ker_le_ker_sigmaW tV θbar σV hcommV) hopenV
  ·
    intro v
    have hιop : ∀ (g : CohCarrier.Gen M' ↑S) (w : Λ),
        CohCarrier.charInvolution M' H' 𝒪 𝒪 (op g • w) = op g • CohCarrier.charInvolution M' H' 𝒪 𝒪 w := by
      intro g w
      rw [hop, hop]
      exact LinearMap.congr_fun (CohCarrier.charInvolution_comp_opFamily M' H' ↑S 𝒪 g) w
    have hιe : CohCarrier.charInvolution M' H' 𝒪 𝒪 (e • v) = e • CohCarrier.charInvolution M' H' 𝒪 𝒪 v :=
      comm_all (CohCarrier.charInvolution M' H' 𝒪 𝒪) op hgen hιop e v
    rw [hΨapp, hΨapp, ← hιe, hΦι _ (hepar v)]
    ext w
    rfl
  ·
    intro μ
    obtain ⟨f, hf⟩ := Subspace.dualRestrict_surjective (W := Wsub) μ
    have hfmem : f ∈ par.map Φ := by rw [hΦsurj]; exact Submodule.mem_top
    obtain ⟨u, hu, rfl⟩ := hfmem
    refine ⟨u, ?_⟩
    rw [hΨapp, hfib e u hu, hθapp, hθe, one_smul, hf]
  ·
    intro m
    constructor
    · intro hm0
      have hm : (m : Λ) ∈ par := by
        rw [← S'.e_smul_coe i₀ m]
        exact hepar _
      have h0 : Wsub.dualRestrict (Φ (m : Λ)) = 0 := by
        rw [← S'.e_smul_coe i₀ m]
        exact hm0
      have hmem := mem_mPar_of_dualRestrict_eq_zero par op θ θbar tV Φ hop_st hθ hΦop hgen hk hΦsurj
        hΦker (m : Λ) hm h0
      have := toCorner_mem_of_mem_mPar S' i₀ πk hk par (m : Λ) hmem
      have hmeq : IharaLemma.toCorner (M := Λ) (S'.e i₀) (m : Λ) = m :=
        Subtype.ext (S'.e_smul_coe i₀ m)
      rwa [hmeq] at this
    · intro hm
      refine Submodule.smul_induction_on
        (p := fun m' : ↥(IharaLemma.cornerSubmodule (M := Λ) (S'.e i₀)) => Ψ (m' : Λ) = 0) hm ?_ ?_
      · intro z hz n _
        change Ψ (((z • n : ↥(IharaLemma.cornerSubmodule (M := Λ) (S'.e i₀))) : Λ)) = 0
        rw [IharaLemma.IdempotentSplitting.coe_cornerSmul, hsemi, toCornerRing_coe,
          (mem_maximalIdeal_iff S' i₀ πk hk z).mp hz, zero_smul]
      · intro x y hx hy
        change Ψ (((x + y : ↥(IharaLemma.cornerSubmodule (M := Λ) (S'.e i₀))) : Λ)) = 0
        rw [Submodule.coe_add, map_add, hx, hy, add_zero]
  ·
    intro ℓ hℓ hℓS hℓM hℓp A hA σ hσ
    have hrel := hES ℓ hℓ hℓS hℓM hℓp A hA σ hσ
    ext w
    have hw : (w : V) ∈ Wsub := w.2
    have h1 := congrArg (fun f : Module.End k V => f (w : V)) hrel
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.zero_apply] at h1
    have hσw : σV σ (w : V) ∈ Wsub := apply_mem_eig tV θbar (σV σ) (fun g => hcommV g σ) hw
    rw [(mem_eig tV θbar).mp hσw, (mem_eig tV θbar).mp hw, smul_smul] at h1
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.zero_apply, Module.End.one_apply, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_smul, Submodule.coe_zero]
    exact h1

end S_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible (solution)

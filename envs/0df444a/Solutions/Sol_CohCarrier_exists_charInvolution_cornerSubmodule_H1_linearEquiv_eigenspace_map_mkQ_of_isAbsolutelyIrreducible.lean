-- Prove2me | solution 1 for CohCarrier.exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c0a49409-aa0d-58a6-aa89-5f9a2b0456db

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_CharInvolution
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_CohCarrier_charInvolution_comp_opFamily
import Theorems.Thm_CohCarrier_exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible
import Theorems.Thm_MonoidHom_exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_Representation_finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.GammaH_finiteIndex AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions"
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.JH.torsionGaloisRep_apply ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply ModularCurve.coe_laurentReductionDegZero ModularCurve.laurentReductionDiv_apply ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq"
p2m_attr_erase "simp" "MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped MatrixGroups

namespace BalanceAssembly

section Lift

variable {𝒪 : Type} [CommRing 𝒪]
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝕋 V] [Module 𝒪 V] [IsScalarTower 𝒪 𝕋 V]

def commSubalg (ι : V →ₗ[𝒪] V) : Subalgebra 𝒪 𝕋 where
  carrier := {t | ∀ v : V, ι (t • v) = t • ι v}
  mul_mem' {a b} ha hb v := by rw [mul_smul, ha, hb, mul_smul]
  one_mem' v := by rw [one_smul, one_smul]
  add_mem' {a b} ha hb v := by rw [add_smul, map_add, ha, hb, add_smul]
  zero_mem' v := by rw [zero_smul, map_zero, zero_smul]
  algebraMap_mem' r v := by rw [algebraMap_smul, algebraMap_smul, map_smul]

theorem comm_all (ι : V →ₗ[𝒪] V) {G : Type} (op : G → 𝕋)
    (hgen : Algebra.adjoin 𝒪 (Set.range op) = ⊤)
    (hcomm : ∀ (g : G) (v : V), ι (op g • v) = op g • ι v) (t : 𝕋) (v : V) :
    ι (t • v) = t • ι v := by
  have hle : Algebra.adjoin 𝒪 (Set.range op) ≤ commSubalg (𝕋 := 𝕋) ι := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨g, rfl⟩
    exact hcomm g
  have ht : t ∈ commSubalg (𝕋 := 𝕋) ι := by
    apply hle
    rw [hgen]
    exact Algebra.mem_top
  exact ht v

variable (Sp : IharaLemma.IdempotentSplitting 𝕋) (i : Fin Sp.n)

def cornerRestrict (ι : V →ₗ[𝒪] V) (hι : ∀ (t : 𝕋) (v : V), ι (t • v) = t • ι v) :
    ↥(IharaLemma.cornerSubmodule (M := V) (Sp.e i)) →ₗ[Sp.CornerRing i]
      ↥(IharaLemma.cornerSubmodule (M := V) (Sp.e i)) where
  toFun m := ⟨ι (m : V), by
    refine ⟨ι (m : V), ?_⟩
    show Sp.e i • ι (m : V) = ι (m : V)
    rw [← hι, Sp.e_smul_coe]⟩
  map_add' m n := Subtype.ext (by
    show ι ((m : V) + (n : V)) = ι (m : V) + ι (n : V)
    rw [map_add])
  map_smul' z m := Subtype.ext (by
    show ι ((z : 𝕋) • (m : V)) = (z : 𝕋) • ι (m : V)
    rw [hι])

@[scoped simp] theorem coe_cornerRestrict (ι : V →ₗ[𝒪] V) (hι : ∀ (t : 𝕋) (v : V), ι (t • v) = t • ι v)
    (m : ↥(IharaLemma.cornerSubmodule (M := V) (Sp.e i))) :
    ((cornerRestrict Sp i ι hι m : ↥(IharaLemma.cornerSubmodule (M := V) (Sp.e i))) : V) = ι (m : V) :=
  rfl

end Lift

section Fibre

variable {A : Type} [CommRing A] [IsLocalRing A]
variable {k : Type} [Field k]
variable (π : A →+* k)
variable {P : Type} [AddCommGroup P] [Module A P]
variable {D : Type} [AddCommGroup D] [Module k D] [FiniteDimensional k D]

@[reducible] def modA (π : A →+* k) (X : Type) [AddCommGroup X] [Module k X] : Module A X :=
  Module.compHom X π

theorem main
    (hπ : Function.Surjective π) (hker : ∀ a : A, π a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A)
    (h2 : (2 : k) ≠ 0)
    (τ : P →ₗ[A] P) (hτ : ∀ m, τ (τ m) = m)
    (u : D →ₗ[k] D)
    (Ψ : P →+ D) (hΨs : ∀ (a : A) (m : P), Ψ (a • m) = π a • Ψ m)
    (hΨτ : ∀ m : P, Ψ (τ m) = u (Ψ m))
    (hΨsurj : Function.Surjective Ψ)
    (hΨker : ∀ m : P, Ψ m = 0 ↔ m ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A P))
    (hbal : Module.finrank k ↥(LinearMap.ker (u - 1)) = Module.finrank k ↥(LinearMap.ker (u + 1))) :
    Nonempty
      (↥((LinearMap.ker (τ - LinearMap.id)).map
          (IsLocalRing.maximalIdeal A • (⊤ : Submodule A P)).mkQ) ≃ₗ[A]
        ↥((LinearMap.ker (τ + LinearMap.id)).map
          (IsLocalRing.maximalIdeal A • (⊤ : Submodule A P)).mkQ)) := by
  classical
  letI : Module A D := modA π D
  letI : Module A k := modA π k
  haveI : IsScalarTower A k D := ⟨fun a x d => by
    show (π a • x) • d = π a • (x • d)
    rw [smul_smul, smul_eq_mul]⟩

  have h2A : IsUnit (2 : A) := by
    by_contra h
    have hmem : (2 : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr h
    have := (hker 2).mpr hmem
    rw [map_ofNat] at this
    exact h2 this
  obtain ⟨half, hhalf⟩ := h2A.exists_left_inv

  let ΨA : P →ₗ[A] D :=
    { toFun := Ψ, map_add' := Ψ.map_add, map_smul' := fun a m => hΨs a m }
  have hΨA : ∀ m, ΨA m = Ψ m := fun _ => rfl
  set N : Submodule A P := IsLocalRing.maximalIdeal A • (⊤ : Submodule A P) with hN
  have hkerA : LinearMap.ker ΨA = N := by
    ext m
    rw [LinearMap.mem_ker, hΨA]
    exact hΨker m
  have hsurjA : Function.Surjective ΨA := hΨsurj

  let Φ : (P ⧸ N) ≃ₗ[A] D :=
    (Submodule.quotEquivOfEq N (LinearMap.ker ΨA) hkerA.symm).trans
      (LinearMap.quotKerEquivOfSurjective ΨA hsurjA)
  have hΦ : ∀ m : P, Φ (N.mkQ m) = Ψ m := by
    intro m
    show (LinearMap.quotKerEquivOfSurjective ΨA hsurjA)
      (Submodule.quotEquivOfEq N (LinearMap.ker ΨA) hkerA.symm (Submodule.Quotient.mk m)) = Ψ m
    rw [Submodule.quotEquivOfEq_mk]
    exact LinearMap.quotKerEquivOfSurjective_apply_mk ΨA hsurjA m

  set Dp : Submodule k D := LinearMap.ker (u - 1) with hDp
  set Dm : Submodule k D := LinearMap.ker (u + 1) with hDm

  have himage_p : ((LinearMap.ker (τ - LinearMap.id)).map N.mkQ).map (Φ : (P ⧸ N) →ₗ[A] D) =
      Dp.restrictScalars A := by
    apply le_antisymm
    · rintro _ ⟨q, ⟨m, hm, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hm
      show Φ (N.mkQ m) ∈ Dp
      rw [hΦ, hDp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← hΨτ, hm]
    · intro f hf
      change f ∈ Dp at hf
      rw [hDp, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hf
      obtain ⟨m, rfl⟩ := hΨsurj f
      refine ⟨N.mkQ (half • (m + τ m)), ⟨half • (m + τ m), ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
          map_smul, map_add, hτ, add_comm]
      · show Φ (N.mkQ (half • (m + τ m))) = Ψ m
        rw [hΦ, hΨs, map_add, hΨτ, hf, ← two_smul k (Ψ m), smul_smul, ← map_ofNat π 2, ← map_mul,
          hhalf, map_one, one_smul]
  have himage_m : ((LinearMap.ker (τ + LinearMap.id)).map N.mkQ).map (Φ : (P ⧸ N) →ₗ[A] D) =
      Dm.restrictScalars A := by
    apply le_antisymm
    · rintro _ ⟨q, ⟨m, hm, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
        add_eq_zero_iff_eq_neg] at hm
      show Φ (N.mkQ m) ∈ Dm
      rw [hΦ, hDm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, ← hΨτ, hm, map_neg,
        neg_add_cancel]
    · intro f hf
      change f ∈ Dm at hf
      rw [hDm, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg] at hf
      obtain ⟨m, rfl⟩ := hΨsurj f
      refine ⟨N.mkQ (half • (m - τ m)), ⟨half • (m - τ m), ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_smul,
          map_sub, hτ, ← smul_add, sub_add_sub_cancel, sub_self, smul_zero]
      · show Φ (N.mkQ (half • (m - τ m))) = Ψ m
        rw [hΦ, hΨs, map_sub, hΨτ, hf, sub_neg_eq_add, ← two_smul k (Ψ m), smul_smul, ← map_ofNat π 2,
          ← map_mul, hhalf, map_one, one_smul]

  let ek : ↥Dp ≃ₗ[k] ↥Dm := LinearEquiv.ofFinrankEq (↥Dp) (↥Dm) hbal
  let eA : ↥Dp ≃ₗ[A] ↥Dm := ek.restrictScalars A

  let rp : ↥(Dp.restrictScalars A) ≃ₗ[A] ↥Dp :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let rm : ↥(Dm.restrictScalars A) ≃ₗ[A] ↥Dm :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

  let e1 : ↥((LinearMap.ker (τ - LinearMap.id)).map N.mkQ) ≃ₗ[A]
      ↥(((LinearMap.ker (τ - LinearMap.id)).map N.mkQ).map (Φ : (P ⧸ N) →ₗ[A] D)) :=
    LinearEquiv.submoduleMap Φ _
  let e2 : ↥((LinearMap.ker (τ + LinearMap.id)).map N.mkQ) ≃ₗ[A]
      ↥(((LinearMap.ker (τ + LinearMap.id)).map N.mkQ).map (Φ : (P ⧸ N) →ₗ[A] D)) :=
    LinearEquiv.submoduleMap Φ _
  exact ⟨e1.trans ((LinearEquiv.ofEq _ _ himage_p).trans (rp.trans (eA.trans (rm.symm.trans
    ((LinearEquiv.ofEq _ _ himage_m).symm.trans e2.symm)))))⟩

theorem finrank_ker_dualMap_eq {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (f : W →ₗ[k] W) :
    Module.finrank k ↥(LinearMap.ker f.dualMap) = Module.finrank k ↥(LinearMap.ker f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f.dualMap
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h1
  omega

end Fibre

section Diamond

open CohCarrier CongruenceSubgroup

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem conjHom_mul (σ₁ σ₂ : Gamma0 M) (γ : ↥(GammaH M H)) :
    conjHom M H (σ₁ * σ₂) γ = conjHom M H σ₁ (conjHom M H σ₂ γ) := by
  apply Subtype.ext
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev]
  simp only [mul_assoc]

variable {𝒪 : Type} [CommRing 𝒪]

theorem diamondRaw_mul (σ₁ σ₂ : Gamma0 M) (φ : H1 M H 𝒪) :
    diamondRaw M H 𝒪 (σ₁ * σ₂) φ = diamondRaw M H 𝒪 σ₂ (diamondRaw M H 𝒪 σ₁ φ) := by
  ext γ
  show φ (Additive.ofMul (conjHom M H (σ₁ * σ₂) (Additive.toMul γ))) =
    φ (Additive.ofMul (conjHom M H σ₁ (Additive.toMul
      (Additive.ofMul (conjHom M H σ₂ (Additive.toMul γ))))))
  rw [toMul_ofMul, conjHom_mul]

theorem diamondL_mul (d₁ d₂ : (ZMod M)ˣ) (φ : H1 M H 𝒪) :
    diamondL M H 𝒪 (d₁ * d₂) φ = diamondL M H 𝒪 d₂ (diamondL M H 𝒪 d₁ φ) := by
  obtain ⟨σ₁, hσ₁⟩ := gamma0Units_surjective M d₁
  obtain ⟨σ₂, hσ₂⟩ := gamma0Units_surjective M d₂
  have h12 : gamma0Units M (σ₁ * σ₂) = d₁ * d₂ := by rw [map_mul, hσ₁, hσ₂]
  rw [diamondL_eq_diamondRaw M H 𝒪 (d₁ * d₂) (σ₁ * σ₂) h12, diamondL_eq_diamondRaw M H 𝒪 d₁ σ₁ hσ₁,
    diamondL_eq_diamondRaw M H 𝒪 d₂ σ₂ hσ₂, diamondRaw_mul]

theorem diamondL_one (φ : H1 M H 𝒪) : diamondL M H 𝒪 1 φ = φ := by
  rw [diamondL_eq_diamondRaw M H 𝒪 1 1 (map_one _)]
  ext γ
  show φ (Additive.ofMul (conjHom M H 1 (Additive.toMul γ))) = φ γ
  have : conjHom M H 1 (Additive.toMul γ) = Additive.toMul γ := by
    apply Subtype.ext
    simp [conjHom]
  rw [this, ofMul_toMul]

theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  simp

theorem gamma0Units_neg_one : gamma0Units M ⟨-1, neg_one_mem_Gamma0 M⟩ = -1 := by
  ext
  simp [gamma0Units, Gamma0Map]

theorem diamondL_neg_one (φ : H1 M H 𝒪) : diamondL M H 𝒪 (-1) φ = φ := by
  rw [diamondL_eq_diamondRaw M H 𝒪 (-1) ⟨-1, neg_one_mem_Gamma0 M⟩ (gamma0Units_neg_one M)]
  ext γ
  show φ (Additive.ofMul (conjHom M H ⟨-1, neg_one_mem_Gamma0 M⟩ (Additive.toMul γ))) = φ γ
  have : conjHom M H ⟨-1, neg_one_mem_Gamma0 M⟩ (Additive.toMul γ) = Additive.toMul γ := by
    apply Subtype.ext
    show (-1) * ((Additive.toMul γ : ↥(GammaH M H)) : SL(2, ℤ)) * (-1)⁻¹ =
      ((Additive.toMul γ : ↥(GammaH M H)) : SL(2, ℤ))
    rw [← neg_inv, inv_one, neg_one_mul, mul_neg_one, neg_neg]
  rw [this, ofMul_toMul]

variable {k : Type} [Field k] [Algebra 𝒪 k]
variable (S : Finset ℕ)
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 M H 𝒪)]

structure DiaData (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ) (𝒪 : Type) [CommRing 𝒪]
    (k : Type) [Field k] [Algebra 𝒪 k]
    (𝕋 : Type) [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (CohCarrier.H1 M H 𝒪)] where
  op : CohCarrier.Gen M ↑S → 𝕋
  θbar : CohCarrier.Gen M ↑S → k
  Sp : IharaLemma.IdempotentSplitting 𝕋
  i : Fin Sp.n
  πk : Sp.CornerRing i →ₐ[𝒪] k
  hfaith : ∀ t : 𝕋, (∀ v : CohCarrier.H1 M H 𝒪, t • v = 0) → t = 0
  hop : ∀ (g : CohCarrier.Gen M ↑S) (v : CohCarrier.H1 M H 𝒪), op g • v = CohCarrier.opFamily M H ↑S 𝒪 g v
  hπk : ∀ g : CohCarrier.Gen M ↑S, πk (Sp.toCornerRing i (op g)) = θbar g

variable {M H S}
variable (X : DiaData M H S 𝒪 k 𝕋)

def DiaData.resT : 𝕋 →+* k := (X.πk : X.Sp.CornerRing X.i →+* k).comp (X.Sp.toCornerRing X.i)

theorem DiaData.resT_op (g : CohCarrier.Gen M ↑S) : X.resT (X.op g) = X.θbar g := X.hπk g

theorem DiaData.op_dia_mul (d₁ d₂ : (ZMod M)ˣ) :
    X.op (Gen.dia (d₁ * d₂)) = X.op (Gen.dia d₂) * X.op (Gen.dia d₁) := by
  rw [← sub_eq_zero]
  apply X.hfaith
  intro v
  rw [sub_smul, mul_smul, X.hop, X.hop, X.hop, sub_eq_zero]
  exact diamondL_mul M H d₁ d₂ v

theorem DiaData.op_dia_one : X.op (Gen.dia (1 : (ZMod M)ˣ)) = 1 := by
  rw [← sub_eq_zero]
  apply X.hfaith
  intro v
  rw [sub_smul, X.hop, one_smul, sub_eq_zero]
  exact diamondL_one M H v

theorem DiaData.op_dia_neg_one : X.op (Gen.dia (-1 : (ZMod M)ˣ)) = 1 := by
  rw [← sub_eq_zero]
  apply X.hfaith
  intro v
  rw [sub_smul, X.hop, one_smul, sub_eq_zero]
  exact diamondL_neg_one M H v

def DiaData.diaHom : (ZMod M)ˣ →* k where
  toFun d := X.θbar (Gen.dia d)
  map_one' := by
    rw [← X.resT_op, X.op_dia_one, map_one]
  map_mul' d₁ d₂ := by
    rw [← X.resT_op, ← X.resT_op, ← X.resT_op, X.op_dia_mul, map_mul, mul_comm]

def DiaData.diaChar : (ZMod M)ˣ →* kˣ := X.diaHom.toHomUnits

theorem DiaData.coe_diaChar (d : (ZMod M)ˣ) : ((X.diaChar d : kˣ) : k) = X.θbar (Gen.dia d) :=
  MonoidHom.coe_toHomUnits _ d

theorem DiaData.diaChar_neg_one : X.diaChar (-1) = 1 := by
  apply Units.ext
  rw [X.coe_diaChar, Units.val_one, ← X.resT_op, X.op_dia_neg_one, map_one]

end Diamond

section Galois

variable {k : Type} [Field k]

local notation "Galℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem isOpen_ker_rho (ρbar : ResidualGaloisRep k) : IsOpen ((ρbar.ρ.ker : Subgroup Galℚ) : Set Galℚ) := by
  obtain ⟨L, hL, hker⟩ := ρbar.factorsThroughFiniteLevel
  haveI : FiniteDimensional ℚ L := hL
  apply Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) _ (IntermediateField.fixingSubgroup_isOpen L)
  intro σ hσ
  rw [MonoidHom.mem_ker]
  exact hker σ ((IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ)

theorem cheb_of_isOpen (H : Subgroup Galℚ) (hH : IsOpen ((H : Subgroup Galℚ) : Set Galℚ))
    (S : Finset ℕ) (σ : Galℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (τ g : Galℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ g * τ * g⁻¹ * σ⁻¹ ∈ H := by
  have hnhds : (H : Set Galℚ) ∈ nhds 1 := hH.mem_nhds H.one_mem
  obtain ⟨E, hEfin, hEnormal, hEH⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ (AlgebraicClosure ℚ) H).mp hnhds
  have halg : (DivisionRing.toRatAlgebra : Algebra ℚ E) = E.algebra := Subsingleton.elim _ _
  haveI hN : @Normal ℚ E _ _ DivisionRing.toRatAlgebra := by rw [halg]; exact hEnormal
  haveI hFD : @FiniteDimensional ℚ E _ _ DivisionRing.toRatAlgebra.toModule := by
    rw [halg]; exact hEfin
  haveI : NumberField E := @NumberField.mk _ _ inferInstance hFD
  haveI : IsGalois ℚ E := ⟨⟩
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) E).ker ≤ H := by
    intro x hx
    apply hEH
    haveI := hEnormal
    rw [← IntermediateField.restrictNormalHom_ker E, SetLike.mem_coe, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hx
    convert hx
    rfl
  exact FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker E hker S σ

theorem quad_transport {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module k W]
    (σW : G →* (W →ₗ[k] W)) (ρm : G →* Matrix (Fin 2) (Fin 2) k) (ψ : G →* kˣ)
    (τ g h g₀ : G) (hg₀ : g₀ = h⁻¹ * (g * τ * g⁻¹))
    (hh1 : σW h = 1) (hh2 : ρm h = 1) (hh3 : ψ h = 1)
    (hann : σW τ ^ 2 - Matrix.trace (ρm τ) • σW τ + ((ψ τ : kˣ) : k) • (1 : W →ₗ[k] W) = 0) :
    σW g₀ ^ 2 - Matrix.trace (ρm g₀) • σW g₀ + ((ψ g₀ : kˣ) : k) • (1 : W →ₗ[k] W) = 0 := by

  have hh1' : σW h⁻¹ = 1 := by
    have := σW.map_mul h⁻¹ h
    rw [inv_mul_cancel, map_one, hh1, mul_one] at this
    exact this.symm
  have hh2' : ρm h⁻¹ = 1 := by
    have := ρm.map_mul h⁻¹ h
    rw [inv_mul_cancel, map_one, hh2, mul_one] at this
    exact this.symm
  set U := σW g with hU
  set U' := σW g⁻¹ with hU'
  set X := σW τ with hX
  have hU'U : U' * U = 1 := by rw [hU, hU', ← map_mul, inv_mul_cancel, map_one]
  have hUU' : U * U' = 1 := by rw [hU, hU', ← map_mul, mul_inv_cancel, map_one]
  have hσ : σW g₀ = U * X * U' := by rw [hg₀, map_mul, hh1', one_mul, map_mul, map_mul]
  have htr : Matrix.trace (ρm g₀) = Matrix.trace (ρm τ) := by
    rw [hg₀, map_mul, hh2', one_mul, map_mul, map_mul, Matrix.trace_mul_comm, ← mul_assoc, ← map_mul,
      inv_mul_cancel, map_one, one_mul]
  have hψ : ψ g₀ = ψ τ := by
    rw [hg₀, map_mul, map_inv, hh3, inv_one, one_mul, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hsq : (U * X * U') ^ 2 = U * X ^ 2 * U' := by
    rw [sq, sq]
    calc U * X * U' * (U * X * U') = U * X * (U' * U) * X * U' := by simp only [mul_assoc]
      _ = U * (X * X) * U' := by rw [hU'U, mul_one]; simp only [mul_assoc]
  rw [hσ, htr, hψ, hsq]
  have := congrArg (fun Y => U * Y * U') hann
  simp only [mul_zero, zero_mul, mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    mul_one] at this
  rw [hUU'] at this
  simpa only [mul_assoc] using this

theorem trace_toMatrixAlgEquiv {V : Type} [AddCommGroup V] [Module k V]
    (b : Module.Basis (Fin 2) k V) (f : V →ₗ[k] V) :
    Matrix.trace (LinearMap.toMatrixAlgEquiv b f) = LinearMap.trace k V f := by
  rw [LinearMap.trace_eq_matrix_trace k b f]
  rfl

theorem dualMap_sub_one {W : Type} [AddCommGroup W] [Module k W] (f : W →ₗ[k] W) :
    f.dualMap - 1 = (f - 1).dualMap := by
  ext g x
  simp [LinearMap.dualMap_apply]

theorem dualMap_add_one {W : Type} [AddCommGroup W] [Module k W] (f : W →ₗ[k] W) :
    f.dualMap + 1 = (f + 1).dualMap := by
  ext g x
  simp [LinearMap.dualMap_apply]

end Galois

end BalanceAssembly
p2m_reactivate "P2MW.S_CohCarrier_exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible.BalanceAssembly"

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 1600000 in
open BalanceAssembly in

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
    ∃ τ : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)) →ₗ[S'.CornerRing i₀]
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
      (∀ m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
        ((τ m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀))) :
          CohCarrier.H1 M' H' 𝒪) = CohCarrier.charInvolution M' H' 𝒪 𝒪 (m : CohCarrier.H1 M' H' 𝒪)) ∧
      Nonempty
        (↥((LinearMap.ker (τ - LinearMap.id)).map
            (IsLocalRing.maximalIdeal (S'.CornerRing i₀) •
              (⊤ : Submodule (S'.CornerRing i₀)
                ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))).mkQ) ≃ₗ[S'.CornerRing i₀]
          ↥((LinearMap.ker (τ + LinearMap.id)).map
            (IsLocalRing.maximalIdeal (S'.CornerRing i₀) •
              (⊤ : Submodule (S'.CornerRing i₀)
                ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)))).mkQ)) := by
  classical

  set ι : CohCarrier.H1 M' H' 𝒪 →ₗ[𝒪] CohCarrier.H1 M' H' 𝒪 := CohCarrier.charInvolution M' H' 𝒪 𝒪 with hιdef
  have hιop : ∀ (g : CohCarrier.Gen M' ↑S) (v : CohCarrier.H1 M' H' 𝒪), ι (op g • v) = op g • ι v := by
    intro g v
    rw [hop, hop]
    exact LinearMap.congr_fun (CohCarrier.charInvolution_comp_opFamily M' H' ↑S 𝒪 g) v
  have hιT : ∀ (t : 𝕋) (v : CohCarrier.H1 M' H' 𝒪), ι (t • v) = t • ι v := comm_all ι op hgen hιop
  let τ := cornerRestrict S' i₀ ι hιT
  have hτι : ∀ m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀)),
      ((τ m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀))) :
        CohCarrier.H1 M' H' 𝒪) = ι (m : CohCarrier.H1 M' H' 𝒪) := fun m => rfl
  have hττ : ∀ m, τ (τ m) = m := by
    intro m
    apply Subtype.ext
    rw [hτι, hτι, hιdef, CohCarrier.charInvolution_charInvolution]
  refine ⟨τ, hτι, ?_⟩

  obtain ⟨W, _instW₁, _instW₂, _instW₃, σW, Ψ, hopenW, hsemi, hΨι, hsurj, hkerΨ, hrel⟩ :=
    CohCarrier.exists_galoisModule_H1_to_dual_charInvolution_frobenius_of_isAbsolutelyIrreducible hk p hp2 M'
      H' S hfaith op hop hgen θbar S' i₀ πk hπk ρbar hirr hatt

  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')

  let X : DiaData M' H' S 𝒪 k 𝕋 :=
    { op := op, θbar := θbar, Sp := S', i := i₀, πk := πk, hfaith := hfaith, hop := hop, hπk := hπk }
  obtain ⟨ψ, hψopen, hψc, hψfrob⟩ :=
    MonoidHom.exists_galoisCharacter_apply_complexConjugation_eq_apply_frobenius_eq_natCast_mul
      (k := k) p M' X.diaChar
  have hψc' : ψ complexConjugation = -1 := by rw [hψc, X.diaChar_neg_one]

  let b : Module.Basis (Fin 2) k ρbar.V := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  let toMat : Module.End k ρbar.V ≃ₐ[k] Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrixAlgEquiv b
  let ρm : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k :=
    toMat.toMulEquiv.toMonoidHom.comp ρbar.ρ
  have hρm : ∀ g, ρm g = toMat (ρbar.ρ g) := fun _ => rfl
  have htrace : ∀ g, Matrix.trace (ρm g) = LinearMap.trace k ρbar.V (ρbar.ρ g) := fun g => by
    rw [hρm]; exact trace_toMatrixAlgEquiv b (ρbar.ρ g)
  have hspan : Submodule.span k (Set.range (fun g => ρm g)) = ⊤ := by
    have h1 : Submodule.span k (Set.range ⇑ρbar.ρ) = ⊤ :=
      (ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρbar).mp hirr
    let L : Module.End k ρbar.V →ₗ[k] Matrix (Fin 2) (Fin 2) k := toMat.toLinearEquiv.toLinearMap
    have h2' : Set.range (fun g => ρm g) = L '' Set.range ⇑ρbar.ρ := by
      rw [← Set.range_comp]
      rfl
    rw [h2', Submodule.span_image, h1, Submodule.map_top]
    exact LinearEquiv.range toMat.toLinearEquiv
  have hkerρ : ρm.ker = ρbar.ρ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρm]
    constructor
    · intro h
      exact toMat.injective (by rw [h, map_one])
    · intro h
      rw [h, map_one]

  have hann : ∀ g₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σW g₀ ^ 2 - Matrix.trace (ρm g₀) • σW g₀ + ((ψ g₀ : kˣ) : k) • (1 : W →ₗ[k] W) = 0 := by
    intro g₀

    set Hsub : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := σW.ker ⊓ ρbar.ρ.ker ⊓ ψ.ker
      with hHsub
    have hHopen : IsOpen ((Hsub : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) := by
      rw [hHsub, Subgroup.coe_inf, Subgroup.coe_inf]
      exact (hopenW.inter (isOpen_ker_rho ρbar)).inter hψopen

    obtain ⟨ℓ, A, τf, g, hℓ, hℓS₀, hA, hτf, hmem⟩ :=
      cheb_of_isOpen Hsub hHopen (insert p (S ∪ M'.primeFactors)) g₀
    have hℓp : ℓ ≠ p := by
      rintro rfl
      exact hℓS₀ (Finset.mem_insert_self _ _)
    have hℓM : ¬ ℓ ∣ M' := fun h =>
      hℓS₀ (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hℓ, h, NeZero.ne M'⟩)))
    have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h =>
      hℓS₀ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_coe.mp h)))

    have hannτ : σW τf ^ 2 - Matrix.trace (ρm τf) • σW τf + ((ψ τf : kˣ) : k) • (1 : W →ₗ[k] W) = 0 := by
      have h := hrel ℓ hℓ hℓS hℓM hℓp A hA τf hτf
      have hcoe : ∀ d : (ZMod M')ˣ, θbar (CohCarrier.Gen.dia d) = ((X.diaChar d : kˣ) : k) :=
        fun d => (X.coe_diaChar d).symm
      rw [← hatt ℓ hℓ hℓS hℓM A hA τf hτf, ← htrace, hcoe, ← hψfrob ℓ hℓ hℓM hℓp A hA τf hτf,
        ← sq] at h
      exact h

    have hmem' := hmem
    rw [hHsub, Subgroup.mem_inf, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker,
      MonoidHom.mem_ker] at hmem'
    obtain ⟨⟨hh1, hh2⟩, hh3⟩ := hmem'
    have hh2' : ρm (g * τf * g⁻¹ * g₀⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hkerρ, MonoidHom.mem_ker]; exact hh2
    refine quad_transport σW ρm ψ τf g (g * τf * g⁻¹ * g₀⁻¹) g₀ ?_ hh1 hh2' hh3 hannτ
    group

  have hbalW : Module.finrank k ↥(LinearMap.ker (σW complexConjugation - 1)) =
      Module.finrank k ↥(LinearMap.ker (σW complexConjugation + 1)) :=
    Representation.finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation ρm σW h2
      hspan ψ hann complexConjugation complexConjugation_mul_self hψc'

  have hbalD : Module.finrank k ↥(LinearMap.ker ((σW complexConjugation).dualMap - 1)) =
      Module.finrank k ↥(LinearMap.ker ((σW complexConjugation).dualMap + 1)) := by
    rw [dualMap_sub_one, dualMap_add_one, finrank_ker_dualMap_eq, finrank_ker_dualMap_eq, hbalW]

  set Pc := IharaLemma.cornerSubmodule (M := CohCarrier.H1 M' H' 𝒪) (S'.e i₀) with hPc

  have hπsurj : Function.Surjective (πk : S'.CornerRing i₀ →+* k) := by
    intro x
    obtain ⟨r, rfl⟩ := hk x
    exact ⟨algebraMap 𝒪 (S'.CornerRing i₀) r, πk.commutes r⟩
  have hπker : ∀ a : S'.CornerRing i₀, (πk : S'.CornerRing i₀ →+* k) a = 0 ↔
      a ∈ IsLocalRing.maximalIdeal (S'.CornerRing i₀) := by
    have hmax : (RingHom.ker (πk : S'.CornerRing i₀ →+* k)) = IsLocalRing.maximalIdeal (S'.CornerRing i₀) :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπsurj)
    intro a
    rw [← hmax, RingHom.mem_ker]

  let ΨP : ↥Pc →+ Module.Dual k W := Ψ.comp Pc.subtype.toAddMonoidHom
  have hΨP : ∀ m : ↥Pc, ΨP m = Ψ (m : CohCarrier.H1 M' H' 𝒪) := fun _ => rfl
  have htoCorner : ∀ a : S'.CornerRing i₀, S'.toCornerRing i₀ (a : 𝕋) = a := by
    intro a
    apply Subtype.ext
    rw [IharaLemma.IdempotentSplitting.coe_toCornerRing, S'.e_mul_coe, S'.coe_mul_e]
  have hΨs : ∀ (a : S'.CornerRing i₀) (m : ↥Pc), ΨP (a • m) = (πk : S'.CornerRing i₀ →+* k) a • ΨP m := by
    intro a m
    rw [hΨP, hΨP, IharaLemma.IdempotentSplitting.coe_cornerSmul, hsemi, htoCorner]
    rfl
  have hΨτ : ∀ m : ↥Pc, ΨP (τ m) = (σW complexConjugation).dualMap (ΨP m) := by
    intro m
    rw [hΨP, hΨP, hτι, hιdef, hΨι]
    rfl
  have hΨsurj : Function.Surjective ΨP := by
    intro f
    obtain ⟨v, rfl⟩ := hsurj f
    refine ⟨⟨S'.e i₀ • v, ⟨v, rfl⟩⟩, ?_⟩
    rw [hΨP]
    show Ψ (S'.e i₀ • v) = Ψ v
    rw [hsemi]
    have : S'.toCornerRing i₀ (S'.e i₀) = 1 := by
      apply Subtype.ext
      rw [IharaLemma.IdempotentSplitting.coe_toCornerRing, (S'.idem i₀).eq, (S'.idem i₀).eq]
      rfl
    rw [this, map_one, one_smul]
  have hΨker : ∀ m : ↥Pc, ΨP m = 0 ↔
      m ∈ IsLocalRing.maximalIdeal (S'.CornerRing i₀) • (⊤ : Submodule (S'.CornerRing i₀) ↥Pc) := by
    intro m
    rw [hΨP]
    exact hkerΨ m
  exact BalanceAssembly.main (πk : S'.CornerRing i₀ →+* k) hπsurj hπker h2 τ hττ
    ((σW complexConjugation).dualMap) ΨP hΨs hΨτ hΨsurj hΨker hbalD

end S_CohCarrier_exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_CohCarrier_exists_charInvolution_cornerSubmodule_H1_linearEquiv_eigenspace_map_mkQ_of_isAbsolutelyIrreducible (solution)

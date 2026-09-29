-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_galoisRepAdic_charpoly_frobenius_eq_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f76b97d9-7454-5fa2-a203-936536999982

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Theorems.Thm_CuspForm_exists_galoisRep_of_point
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_integralClosure_coe_eq_qCoeff_nat
import Theorems.Thm_CuspForm_finiteDimensional_adjoin_qCoeff
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_galoisRepAdic_charpoly_frobenius_eq_of_isMaximal
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D"
p2m_attr_erase "simp" "ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open Polynomial NumberField IsDedekindDomain

noncomputable section

namespace LambdaAdicFamily

section CoefficientRing

variable {N : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2}

abbrev coeffOrder (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Subalgebra ℤ ℂ :=
  Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)

abbrev heckeField (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)

theorem coeffOrder_le_heckeField :
    ∀ x : ℂ, x ∈ coeffOrder g → x ∈ heckeField g := by
  intro x hx
  have hle : coeffOrder g ≤ (heckeField g).toSubalgebra.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    intro y hy
    exact IntermediateField.subset_adjoin ℚ _ hy
  exact hle hx

def toHeckeField : coeffOrder g →+* heckeField g where
  toFun x := ⟨x.1, coeffOrder_le_heckeField x.1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toHeckeField_injective : Function.Injective (toHeckeField (g := g)) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : heckeField g => (z : ℂ)) h)

theorem isIntegral_int_of_injective {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    (f : A →+* B) (hf : Function.Injective f) {a : A} (h : IsIntegral ℤ (f a)) : IsIntegral ℤ a := by
  obtain ⟨q, hq, hqa⟩ := h
  refine ⟨q, hq, hf ?_⟩
  rw [map_zero, Polynomial.hom_eval₂, ← hqa]
  congr 1
  exact RingHom.ext_int _ _

variable [NeZero N]

theorem isIntegral_of_mem_coeffOrder (hg : g.IsNormalizedEigenform) (x : ℂ) (hx : x ∈ coeffOrder g) :
    IsIntegral ℤ x := by
  have hle : coeffOrder g ≤ integralClosure ℤ ℂ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨n, rfl⟩
    obtain ⟨b, hb⟩ := CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff_nat
      (CuspForm.hasIntegralStructure_two N) hg n
    show ModularFormClass.qCoeff g n ∈ integralClosure ℤ ℂ
    rw [← hb]; exact b.2
  exact hle hx

theorem isIntegral_toHeckeField {inst : Algebra ℤ (heckeField g)} (hg : g.IsNormalizedEigenform)
    (x : coeffOrder g) : @IsIntegral ℤ (heckeField g) _ _ inst (toHeckeField x) :=
  @isIntegral_int_of_injective _ _ _ _ inst _ (heckeField g).val.toRingHom Subtype.val_injective _
    (isIntegral_of_mem_coeffOrder hg x.1 x.2)

def toRingOfIntegers (hg : g.IsNormalizedEigenform) : coeffOrder g →+* 𝓞 (heckeField g) where
  toFun x := ⟨toHeckeField x, isIntegral_toHeckeField hg x⟩
  map_one' := RingOfIntegers.eq_iff.mp rfl
  map_mul' _ _ := RingOfIntegers.eq_iff.mp rfl
  map_zero' := RingOfIntegers.eq_iff.mp rfl
  map_add' _ _ := RingOfIntegers.eq_iff.mp rfl

theorem coe_toRingOfIntegers (hg : g.IsNormalizedEigenform) (x : coeffOrder g) :
    ((toRingOfIntegers hg x : 𝓞 (heckeField g)) : heckeField g) = toHeckeField x := rfl

theorem toRingOfIntegers_injective (hg : g.IsNormalizedEigenform) :
    Function.Injective (toRingOfIntegers hg) := by
  intro x y h
  apply toHeckeField_injective
  have := congrArg (fun z : 𝓞 (heckeField g) => (z : heckeField g)) h
  simpa [coe_toRingOfIntegers] using this

theorem numberField_heckeField (hg : g.IsNormalizedEigenform) : NumberField (heckeField g) :=
  { to_charZero := inferInstance
    to_finiteDimensional := CuspForm.finiteDimensional_adjoin_qCoeff hg }

end CoefficientRing

section Completion

variable {N : ℕ} [NeZero N] {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2}

theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff
    {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  change ¬ Valued.v ((algebraMap R K r : K) : v.adicCompletion K) = 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact ⟨fun h => lt_of_le_of_ne (HeightOneSpectrum.valuation_le_one v r) h, fun h => h.ne⟩

theorem exists_coefficientRing (hg : g.IsNormalizedEigenform)
    (P : Ideal (coeffOrder g)) (hP : P.IsMaximal) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (O : Type) (_ : CommRing O) (_ : IsDomain O)
      (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
      (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
      (ι : coeffOrder g →+* O),
      (p : coeffOrder g) ∈ P ∧ (p : O) ∈ IsLocalRing.maximalIdeal O ∧
      Function.Injective ι ∧ Ideal.comap ι (IsLocalRing.maximalIdeal O) = P := by
  classical
  haveI : NumberField (heckeField g) := numberField_heckeField hg
  set K := heckeField g
  haveI := hP

  letI : Algebra (coeffOrder g) (𝓞 K) := (toRingOfIntegers hg).toAlgebra
  have halg : ∀ x, algebraMap (coeffOrder g) (𝓞 K) x = toRingOfIntegers hg x := fun _ => rfl
  haveI : IsScalarTower ℤ (coeffOrder g) (𝓞 K) :=
    IsScalarTower.of_algebraMap_eq (fun n => by simp)
  haveI : Algebra.IsIntegral (coeffOrder g) (𝓞 K) :=
    ⟨fun y => (RingOfIntegers.isIntegral y).tower_top⟩

  have hker : RingHom.ker (algebraMap (coeffOrder g) (𝓞 K)) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (toRingOfIntegers_injective hg)
  obtain ⟨Q, hQmax, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral P (S := 𝓞 K)
    (by rw [hker]; exact bot_le)
  have hQne : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQmax (RingOfIntegers.not_isField K)
  let v : HeightOneSpectrum (𝓞 K) := ⟨Q, hQmax.isPrime, hQne⟩

  haveI : Finite (𝓞 K ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQne
  haveI : Field (𝓞 K ⧸ Q) := Ideal.Quotient.field Q
  obtain ⟨p, hpchar⟩ := CharP.exists (𝓞 K ⧸ Q)
  have hp : p.Prime := CharP.char_is_prime (𝓞 K ⧸ Q) p
  have hpQ : (p : 𝓞 K) ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (𝓞 K ⧸ Q) p
  have hpP : (p : coeffOrder g) ∈ P := by
    rw [← hQP, Ideal.mem_comap, map_natCast]; exact hpQ

  let O : Type := v.adicCompletionIntegers K
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) O :=
    HeightOneSpectrum.isAdicComplete_adicCompletionIntegers K v
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := ‹Finite (𝓞 K ⧸ Q)›
  haveI : Finite (IsLocalRing.ResidueField O) :=
    HeightOneSpectrum.finite_residueField_adicCompletionIntegers K v
  haveI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero O := inferInstance
  let ι : coeffOrder g →+* O := (algebraMap (𝓞 K) O).comp (toRingOfIntegers hg)
  have hmem : ∀ x : coeffOrder g, ι x ∈ IsLocalRing.maximalIdeal O ↔ x ∈ P := by
    intro x
    show algebraMap (𝓞 K) O (toRingOfIntegers hg x) ∈ _ ↔ _
    rw [algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff K v, ← hQP, Ideal.mem_comap]
    rfl
  refine ⟨p, ⟨hp⟩, O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ι, hpP, ?_, ?_, ?_⟩
  · have := (hmem (p : coeffOrder g)).mpr hpP
    rwa [map_natCast] at this
  · exact (FaithfulSMul.algebraMap_injective (𝓞 K) O).comp (toRingOfIntegers_injective hg)
  · ext x; rw [Ideal.mem_comap]; exact hmem x

end Completion

section Main

variable {N : ℕ} [NeZero N] {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2}

theorem eigenchar_mem_coeffOrder (S : Set ℕ) (χ : CuspForm.heckeAlgebra N 2 S →+* ℂ)
    (hχT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = ModularFormClass.qCoeff g ℓ)
    (hχU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
      χ (CuspForm.heckeAlgebra.U hq hqN hqS) = ModularFormClass.qCoeff g q)
    (t : CuspForm.heckeAlgebra N 2 S) : χ t ∈ coeffOrder g := by
  obtain ⟨x, hx⟩ := t
  have hx' : x ∈ Algebra.adjoin ℤ (CuspForm.heckeGenerators N 2 S) := hx
  induction hx' using Algebra.adjoin_induction with
  | mem x hxs =>
    rcases hxs with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
    · have h : (⟨CuspForm.heckeTLin 2 hℓ hℓN, hx⟩ : CuspForm.heckeAlgebra N 2 S) =
          CuspForm.heckeAlgebra.T hℓ hℓN hℓS := rfl
      rw [h, hχT]
      exact Algebra.subset_adjoin ⟨ℓ, rfl⟩
    · have h : (⟨CuspForm.heckeULin 2 hqN, hx⟩ : CuspForm.heckeAlgebra N 2 S) =
          CuspForm.heckeAlgebra.U hq hqN hqS := rfl
      rw [h, hχU]
      exact Algebra.subset_adjoin ⟨q, rfl⟩
  | algebraMap r =>
    have h : (⟨algebraMap ℤ _ r, hx⟩ : CuspForm.heckeAlgebra N 2 S) =
        (r : CuspForm.heckeAlgebra N 2 S) := by
      apply Subtype.ext
      simp
    rw [h, map_intCast]
    exact intCast_mem _ r
  | add x y hx₁ hy₁ ihx ihy =>
    have h : (⟨x + y, hx⟩ : CuspForm.heckeAlgebra N 2 S) = ⟨x, hx₁⟩ + ⟨y, hy₁⟩ := rfl
    rw [h, map_add]
    exact add_mem (ihx hx₁) (ihy hy₁)
  | mul x y hx₁ hy₁ ihx ihy =>
    have h : (⟨x * y, hx⟩ : CuspForm.heckeAlgebra N 2 S) = ⟨x, hx₁⟩ * ⟨y, hy₁⟩ := rfl
    rw [h, map_mul]
    exact mul_mem (ihx hx₁) (ihy hy₁)

theorem main (hg : g.IsNormalizedEigenform)
    (P : Ideal (Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)))
    (hP : P.IsMaximal) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (O : Type) (_ : CommRing O) (_ : IsDomain O)
      (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
      (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
      (ι : Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n) →+* O)
      (ρ : GaloisRepAdic O),
      ((p : ℕ) : Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)) ∈ P ∧
      (p : O) ∈ IsLocalRing.maximalIdeal O ∧
      Function.Injective ι ∧
      Ideal.comap ι (IsLocalRing.maximalIdeal O) = P ∧
      (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (ι ⟨ModularFormClass.qCoeff g ℓ, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩) * X
                + C ((ℓ : O))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ρ.IsUnramifiedAt ℓ) := by
  classical
  obtain ⟨p, hpF, O', _, _, _, _, _, _, ι₁, hpP, hpO', hι₁, hcomap⟩ :=
    exists_coefficientRing hg P hP

  let S₀ : Finset ℕ := insert p N.primeFactors
  have hpS : p ∈ S₀ := Finset.mem_insert_self _ _
  have hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S₀ := fun q hq hqN =>
    Finset.mem_insert_of_mem (Nat.mem_primeFactors.2 ⟨hq, hqN, NeZero.ne N⟩)
  obtain ⟨χ, -, hχT, hχU⟩ := hg.exists_ringHom_heckeAlgebra (↑S₀ : Set ℕ)
  have hχmem := eigenchar_mem_coeffOrder (g := g) (↑S₀ : Set ℕ) χ hχT hχU
  let χR : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* coeffOrder g :=
    χ.codRestrict (coeffOrder g) hχmem
  let χ' : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* O' := ι₁.comp χR
  have hpt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S₀ : Set ℕ)),
      χ' (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) =
        ι₁ ⟨ModularFormClass.qCoeff g ℓ, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩ := by
    intro ℓ hℓ hℓN hℓS
    show ι₁ (χR _) = _
    congr 1
    exact Subtype.ext (hχT ℓ hℓ hℓN hℓS)

  obtain ⟨O, _, _, _, _, _, _, _, _, _, hinj, ρ, hchar, hunr⟩ :=
    CuspForm.exists_galoisRep_of_point p N S₀ hpS hNS O' hpO' χ'
  refine ⟨p, hpF, O, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (algebraMap O' O).comp ι₁, ρ, hpP, ?_, hinj.comp hι₁, ?_, ?_, hunr⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap O' O) p,
      isUnit_map_iff, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact hpO'
  · ext x
    rw [← hcomap, Ideal.mem_comap, Ideal.mem_comap, RingHom.comp_apply,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]
  · intro ℓ hℓ hℓN hℓp A hA σ hσ
    have hℓS : ℓ ∉ (↑S₀ : Set ℕ) := by
      simp only [S₀, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Nat.mem_primeFactors,
        not_or, not_and]
      exact ⟨hℓp, fun _ h _ => hℓN h⟩
    rw [hchar ℓ hℓ hℓN hℓS A hA σ hσ, hpt]
    rfl

end Main

end LambdaAdicFamily

end

open Polynomial in
theorem solution
    {N : ℕ} [NeZero N] {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hg : g.IsNormalizedEigenform)
    (P : Ideal (Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)))
    (hP : P.IsMaximal) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (O : Type) (_ : CommRing O) (_ : IsDomain O)
      (_ : IsDiscreteValuationRing O) (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
      (_ : Finite (IsLocalRing.ResidueField O)) (_ : CharZero O)
      (ι : Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n) →+* O)
      (ρ : GaloisRepAdic O),
      ((p : ℕ) : Algebra.adjoin ℤ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)) ∈ P ∧
      (p : O) ∈ IsLocalRing.maximalIdeal O ∧
      Function.Injective ι ∧
      Ideal.comap ι (IsLocalRing.maximalIdeal O) = P ∧
      (∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ.ρ σ) =
              X ^ 2 - C (ι ⟨ModularFormClass.qCoeff g ℓ, Algebra.subset_adjoin ⟨ℓ, rfl⟩⟩) * X
                + C ((ℓ : O))) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p → ρ.IsUnramifiedAt ℓ) :=
  LambdaAdicFamily.main hg P hP

end S_CuspForm_IsNormalizedEigenform_exists_galoisRepAdic_charpoly_frobenius_eq_of_isMaximal
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_galoisRepAdic_charpoly_frobenius_eq_of_isMaximal (solution)

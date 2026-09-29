-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_algHom_moduleEnd_baseML_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6cdb380c-9533-5757-a2d0-cda1e0839e01

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_AuxLevelHeckeModuleBase
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CuspForm_heckeLocal_exists_algEquiv_cornerRing_baseHeckeData_of_not_isEisenstein
import Theorems.Thm_CuspForm_heckeLocal_exists_algHom_of_subset
import Theorems.Thm_CuspForm_heckeLocal_bijective_of_subset_of_forall_prime_mem_of_charpoly_frobenius_eq
import Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
import Theorems.Thm_CohCarrier_HeckeData_nonempty_idempotentSplitting_opSubalgebra
import Theorems.Thm_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_algHom_moduleEnd_baseML_injective
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow Deformation.ProartinianCat.instCategory Deformation.ProartinianCat.topologicalSpace Deformation.ProartinianCat.instUniqueHomSelf Deformation.IsLocalProartinianAlgebra.toIsLocalHom Deformation.ProartinianCat.instDiscreteTopologyCarrierResidueField Deformation.ProartinianCat.algebra Deformation.IsLocalProartinianAlgebra.toIsLocalRing Deformation.IsLocalProartinianAlgebra.toIsProartinian Deformation.IsLocalProartinianAlgebra.toIsTopologicalRing Deformation.ProartinianCat.instCoeSortType Deformation.ProartinianCat.instUniqueHomResidueField Deformation.ProartinianCat.instIsLocalHomCarrierContinuousAlgHomHom Deformation.IsLocalProartinianAlgebra.toIsResidueAlgebra Deformation.ProartinianCat.isLocalProartinianAlgebra Deformation.ProartinianCat.instIsAdicTopologyCarrierSelf Deformation.ProartinianCat.commRing Deformation.ProartinianCat.instFieldCarrierResidueField IsLocalRing.instDiscreteTopologyQuotientIdealHPowNatMaximalIdeal_definitions IsLocalRing.instIsLinearTopology_definitions IsProartinian.toT0Space instIsProartinianOfDiscreteTopologyOfIsArtinianRing IsLocalRing.instIsAdicTopology instIsProartinianOfIsAdicTopologyOfIsNoetherianRingOfCompactSpace IsLocalRing.instIsHausdorffMaximalIdealOfIsNoetherianRing_definitions"
p2m_attr_erase "instance" "IsLocalRing.instNonarchimedeanRing_definitions IsLocalRing.instIsPrecompleteMaximalIdealOfCompactSpace_definitions IsLocalRing.instDiscreteTopologyOfIsArtinianRing_definitions IsLocalRing.instT2SpaceOfIsNoetherianRing_definitions IsProartinian.toCompleteSpace IsProartinian.toIsLinearTopology instTopologicallyFGOfFiniteType instMulSemiringActionSubtypeMemIntermediateFieldOfSMulCommClassOfNormal_definitions instIsLocalHomRingHomAlgebraMap_definitions instContinuousConstSMulConjActOfContinuousMul_definitions instIsLocalHomRingHomToRingHom_definitions_1 instIsLocalHomResidueFieldRingHomAlgebraMap_definitions instMulSemiringActionRingOfIntegers_definitions instIsLocalHomRingHomToRingHom_definitions instMulActionContinuousMonoidHomOfContinuousConstSMul_definitions instFiniteIndexMulOppositeOp_definitions ValuationSubring.smulCommClass instFaithfulSMulSubtypeMemValuationSubring_definitions ContinuousAlgHom.isLocalHom_id instIsModuleTopologyMatrixOfFiniteOfIsTopologicalRing_definitions IsTopologicalAddGroup.discreteUniformity IntermediateField.smulCommClass_of_normal instMulActionMonoidHomOfMulDistribMulAction_definitions IsTopologicalGroup.discreteUniformity instIsLocalHomRingHomOfContinuousAlgHom_definitions Additive.instDistrbMulAction instIsLocalHomRingHomOfContinuousAlgHom_definitions_1 instNumberFieldSubtypeMemIntermediateFieldOfFiniteDimensional_definitions ContinuousAlgHom.isLocalHom_comp instIsLocalHomContinuousAlgHomToContinuousAlgHom_definitions IsResidueAlgebra.inst IsResidueAlgebra.instQuotientIdeal IsLocalRing.quot IsLocalHom.quotient_mk Deformation.ProartinianCat.ClosedSubalgebra.instNontrivialSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsLinearTopologySubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsTopologicalRingSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace TateModule.instModule"
p2m_attr_erase "instance" "TateModule.instSMul AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec Deformation.ProartinianCat.Hom.mk.injEq Deformation.ProartinianCat.ofHom_comp Deformation.ProartinianCat.hom_comp Deformation.ProartinianCat.mk.sizeOf_spec Deformation.ProartinianCat.Hom.mk.sizeOf_spec Deformation.ProartinianCat.ofEquiv_hom_hom Deformation.ProartinianCat.ofHom_id Deformation.ProartinianCat.hom_id Deformation.ProartinianCat.ofEquiv_inv_hom Deformation.ProartinianCat.mk.injEq Deformation.ProartinianCat.ofHom_hom ContinuousMonoidHom.val_inv_toHomUnits_toFun Units.val_mapₜ_toFun MonoidHom.coe_smul ContinuousAlgHom.coe_toContinuousMonoidHom ContinuousMonoidHom.val_toHomUnits_toFun ContinuousMonoidHom.mk_toMonoidHom ContinuousAlgHom.mapMatrix_apply Units.val_inv_mapₜ_toFun Units.coeHomₜ_toFun ContinuousMonoidHom.coe_mk ContinuousMonoidHom.coe_smul Deformation.repnFunctor_map Deformation.mapRepn_apply Deformation.ProartinianCat.closedSubalgebraι_apply Deformation.matrixRepresentation_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V"
p2m_attr_erase "simp" "TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight"
p2m_attr_erase "simp" "AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_heckeULowerLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_traceLin_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Polynomial IsLocalRing

noncomputable section

namespace EscompES

open IharaLemma CuspForm CuspForm.AuxLevel

section NonEis

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem exists_nonEis_prime
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (N : ℕ) [NeZero N] (r : ℕ)
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪)) :
    ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ℓ ≠ r ∧ ℓ ≡ 1 [MOD N] ∧
        θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ≠ (ℓ : ResidueField 𝒪) + 1 := by
  classical

  set f : ℕ → ℕ := fun q => if q = 0 then 1 else q with hfdef
  have hfpos : ∀ q, 0 < f q := fun q => by
    by_cases hq : q = 0
    · rw [hfdef]; simp [hq]
    · rw [hfdef]; simp only [hq, if_false]; exact Nat.pos_of_ne_zero hq
  set M₀ : ℕ := N * ∏ q ∈ insert r S, f q with hM₀def
  have hM₀ : 0 < M₀ := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) (Finset.prod_pos fun q _ => hfpos q)
  obtain ⟨ℓ, A, σ, hℓ, hℓM, hmod, hA, hσ, heval⟩ :=
    ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
      ρbar habs N hM₀
  have hℓN : ¬ ℓ ∣ N := fun h => hℓM (h.trans (Dvd.intro _ rfl))

  have havoid : ∀ q ∈ insert r S, ℓ ≠ q := by
    intro q hq hℓq
    by_cases hq0 : q = 0
    · exact hℓ.ne_zero (hℓq.trans hq0)
    · apply hℓM
      have h1 : f q ∣ ∏ q ∈ insert r S, f q := Finset.dvd_prod_of_mem f hq
      have h2 : f q = q := by rw [hfdef]; simp [hq0]
      rw [h2] at h1
      rw [hℓq]
      exact h1.trans (Dvd.intro_left _ rfl)
  have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h => havoid ℓ (Finset.mem_insert_of_mem h) rfl
  have hℓr : ℓ ≠ r := fun h => havoid r (Finset.mem_insert_self r S) h
  refine ⟨ℓ, hℓ, hℓN, hℓS, hℓr, hmod, fun heq => heval ?_⟩
  rw [hθ ℓ hℓ hℓN hℓS A hA σ hσ, heq]
  simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C]
  ring

end NonEis

section Corner

variable (𝒪 : Type) [CommRing 𝒪]

def toCornerAlgHom {B : Type} [CommRing B] [Algebra 𝒪 B] (Sp : IdempotentSplitting B)
    (i : Fin Sp.n) : B →ₐ[𝒪] Sp.CornerRing i :=
  { Sp.toCornerRing i with commutes' := fun _ => rfl }

@[scoped simp] theorem toCornerAlgHom_apply {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Sp : IdempotentSplitting B) (i : Fin Sp.n) (b : B) :
    toCornerAlgHom 𝒪 Sp i b = Sp.toCornerRing i b := rfl

theorem mem_𝔪_iff {B : Type} [CommRing B] [Algebra 𝒪 B] {k : Type} [Field k] [Algebra 𝒪 k]
    (Sp : IdempotentSplitting B) (i : Fin Sp.n) (hk : Function.Surjective (algebraMap 𝒪 k))
    (πk : Sp.CornerRing i →ₐ[𝒪] k) (b : B) :
    πk (Sp.toCornerRing i b) = 0 ↔ b ∈ Sp.𝔪 i := by
  let χ : B →ₐ[𝒪] k := πk.comp (toCornerAlgHom 𝒪 Sp i)
  have hχsurj : Function.Surjective χ := fun y => by
    obtain ⟨a, rfl⟩ := hk y
    exact ⟨algebraMap 𝒪 B a, χ.commutes a⟩
  have hmax : (RingHom.ker χ.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective χ.toRingHom hχsurj
  obtain ⟨j, hj⟩ := Sp.exists_eq _ hmax
  have hji : j = i := by
    by_contra hne
    have hmem : Sp.e i ∈ Sp.𝔪 j := Sp.mem_of_ne fun h => hne h.symm
    rw [hj, RingHom.mem_ker] at hmem
    have h1 : Sp.toCornerRing i (Sp.e i) = 1 := by
      apply Subtype.ext
      show Sp.e i * Sp.e i * Sp.e i = Sp.e i
      rw [(Sp.idem i).eq, (Sp.idem i).eq]
    have : χ (Sp.e i) = 1 := by
      show πk (Sp.toCornerRing i (Sp.e i)) = 1
      rw [h1, map_one]
    rw [show χ.toRingHom (Sp.e i) = χ (Sp.e i) from rfl, this] at hmem
    exact one_ne_zero hmem
  subst hji
  rw [hj, RingHom.mem_ker]
  rfl

theorem cornerSmul_injective {B : Type} [CommRing B]
    {V : Type} [AddCommGroup V] [Module B V]
    (hfaith : ∀ b b' : B, (∀ v : V, b • v = b' • v) → b = b')
    (Sp : IdempotentSplitting B) (i : Fin Sp.n) (z w : Sp.CornerRing i)
    (hzw : ∀ y : ↥(cornerSubmodule (M := V) (Sp.e i)), z • y = w • y) : z = w := by
  have hzB : (z : B) = w := by
    apply hfaith
    intro v
    have h := congrArg Subtype.val (hzw (toCorner (M := V) (Sp.e i) v))
    rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_cornerSmul, toCorner_apply,
      smul_smul, smul_smul, Sp.coe_mul_e, Sp.coe_mul_e] at h
    exact h
  exact Subtype.ext hzB

end Corner

section Concrete

open scoped IsMulCommutative

variable (N : ℕ) [NeZero N] (S : Finset ℕ) (r : ℕ)
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
variable (θ : ↥(heckeAlgebra N 2 (↑S : Set ℕ)) →+* ResidueField 𝒪)
variable (hc₀ : BaseOpComm N r (↑S : Set ℕ) 𝒪)

local notation3 "𝔇" => baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀
local notation3 "𝕍" => CohCarrier.H1 N ⊤ 𝒪

abbrev opGen (g : Gen N r (↑S : Set ℕ)) : ↥(𝔇).opSubalgebra :=
  ⟨(𝔇).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

def φ : (𝔇).FreeAlg →ₐ[𝒪] ↥(𝔇).opSubalgebra :=
  MvPolynomial.aeval fun g => opGen N S r 𝒪 θ hc₀ g

theorem φ_X (g : Gen N r (↑S : Set ℕ)) :
    φ N S r 𝒪 θ hc₀ (MvPolynomial.X g) = opGen N S r 𝒪 θ hc₀ g :=
  MvPolynomial.aeval_X _ g

theorem smul_eq_φ_smul (f : (𝔇).FreeAlg) (v : 𝕍) : f • v = (φ N S r 𝒪 θ hc₀ f) • v := rfl

theorem φ_surjective : Function.Surjective (φ N S r 𝒪 θ hc₀) := by
  intro x
  have hle : Algebra.adjoin 𝒪 (Subtype.val ⁻¹' Set.range (𝔇).op : Set ↥(𝔇).opSubalgebra) ≤
      (φ N S r 𝒪 θ hc₀).range :=
    Algebra.adjoin_le (by
      rintro y ⟨g, hg⟩
      refine ⟨MvPolynomial.X g, ?_⟩
      show φ N S r 𝒪 θ hc₀ (MvPolynomial.X g) = y
      rw [φ_X]
      exact Subtype.ext hg)
  have htop : Algebra.adjoin 𝒪 (Subtype.val ⁻¹' Set.range (𝔇).op : Set ↥(𝔇).opSubalgebra) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  have hx : x ∈ (φ N S r 𝒪 θ hc₀).range := hle (by rw [htop]; exact Algebra.mem_top)
  exact hx

variable (Sp : IdempotentSplitting ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra)
  (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
  (hπk : ∀ g : Gen N r (↑S : Set ℕ), πk (Sp.toCornerRing i₀ (opGen N S r 𝒪 θ hc₀ g)) =
    θ (heckeAlgebra.T g.prime g.not_dvd g.notMem))

local notation3 "ℙ" => ↥(cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))

include hπk in

theorem πk_toCornerRing_φ (f : (𝔇).FreeAlg) :
    πk (Sp.toCornerRing i₀ (φ N S r 𝒪 θ hc₀ f)) = (𝔇).thetaTilde f := by
  have heq : (πk.comp ((toCornerAlgHom 𝒪 Sp i₀).comp (φ N S r 𝒪 θ hc₀))) = (𝔇).thetaTilde := by
    apply MvPolynomial.algHom_ext
    intro g
    rw [AlgHom.comp_apply, AlgHom.comp_apply, toCornerAlgHom_apply, φ_X, hπk]
    show _ = MvPolynomial.aeval (𝔇).θbar (MvPolynomial.X g)
    rw [MvPolynomial.aeval_X]
    rfl
  exact congrArg (fun ψ : (𝔇).FreeAlg →ₐ[𝒪] ResidueField 𝒪 => ψ f) heq

include hπk in

theorem mem_mTheta_iff (f : (𝔇).FreeAlg) :
    f ∈ (𝔇).mTheta ↔ φ N S r 𝒪 θ hc₀ f ∈ Sp.𝔪 i₀ := by
  have hk : Function.Surjective (algebraMap 𝒪 (ResidueField 𝒪)) := Ideal.Quotient.mk_surjective
  rw [← mem_𝔪_iff 𝒪 Sp i₀ hk πk, πk_toCornerRing_φ N S r 𝒪 θ hc₀ Sp i₀ πk hπk]
  exact RingHom.mem_ker

@[reducible] def modP : Module (𝔇).FreeAlg ℙ := Module.compHom _ (φ N S r 𝒪 θ hc₀).toRingHom

attribute [local instance] modP

theorem freeAlg_smul_P (f : (𝔇).FreeAlg) (y : ℙ) : f • y = (φ N S r 𝒪 θ hc₀ f) • y := rfl

scoped instance towerP : IsScalarTower 𝒪 (𝔇).FreeAlg ℙ :=
  ⟨fun a f y => by
    rw [freeAlg_smul_P, freeAlg_smul_P, map_smul, smul_assoc]⟩

def fL : 𝕍 →ₗ[(𝔇).FreeAlg] ℙ where
  toFun := toCorner (M := 𝕍) (Sp.e i₀)
  map_add' v w := map_add _ v w
  map_smul' f v := by
    apply Subtype.ext
    rw [RingHom.id_apply, freeAlg_smul_P, Submodule.coe_smul, toCorner_apply, toCorner_apply,
      smul_eq_φ_smul, smul_smul, smul_smul, mul_comm]

theorem fL_apply (v : 𝕍) : fL N S r 𝒪 θ hc₀ Sp i₀ v = toCorner (M := 𝕍) (Sp.e i₀) v := rfl

include hπk in

theorem isLocalizedModule_fL : IsLocalizedModule (𝔇).mTheta.primeCompl (fL N S r 𝒪 θ hc₀ Sp i₀) := by
  have h₂ := Sp.isLocalizedModule_toCorner_maximalIdeal i₀ (M := 𝕍)
  have hmem := mem_mTheta_iff N S r 𝒪 θ hc₀ Sp i₀ πk hπk
  refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
  ·
    have hs : φ N S r 𝒪 θ hc₀ (s : (𝔇).FreeAlg) ∉ Sp.𝔪 i₀ := fun h => s.2 ((hmem _).mpr h)
    have hb := (Module.End.isUnit_iff _).mp (h₂.map_units ⟨_, hs⟩)
    exact (Module.End.isUnit_iff _).mpr hb
  ·
    refine ⟨((y : 𝕍), 1), ?_⟩
    show ((1 : (𝔇).mTheta.primeCompl) : (𝔇).FreeAlg) • y = fL N S r 𝒪 θ hc₀ Sp i₀ (y : 𝕍)
    rw [OneMemClass.coe_one, one_smul]
    exact (Subtype.ext (Sp.e_smul_coe i₀ y)).symm
  ·
    obtain ⟨c, hc⟩ := h₂.exists_of_eq h
    obtain ⟨t, ht⟩ := φ_surjective N S r 𝒪 θ hc₀ (c : ↥(𝔇).opSubalgebra)
    have htm : t ∉ (𝔇).mTheta := fun htm => c.2 (ht ▸ (hmem t).mp htm)
    refine ⟨⟨t, htm⟩, ?_⟩
    show t • x₁ = t • x₂
    rw [smul_eq_φ_smul, smul_eq_φ_smul, ht]
    exact hc

include hπk in

theorem exists_linearEquiv_baseML_corner :
    ∃ Φ : baseML N r (↑S : Set ℕ) 𝒪 θ hc₀ ≃ₗ[(𝔇).FreeAlg] ℙ, True := by
  haveI := isLocalizedModule_fL N S r 𝒪 θ hc₀ Sp i₀ πk hπk
  exact ⟨IsLocalizedModule.iso (𝔇).mTheta.primeCompl (fL N S r 𝒪 θ hc₀ Sp i₀), trivial⟩

theorem cornerT_smul (g : Gen N r (↑S : Set ℕ)) (y : ℙ) :
    (Sp.toCornerRing i₀ (opGen N S r 𝒪 θ hc₀ g)) • y = (MvPolynomial.X g : (𝔇).FreeAlg) • y := by
  apply Subtype.ext
  rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_toCornerRing, freeAlg_smul_P,
    φ_X, Submodule.coe_smul, mul_comm (Sp.e i₀), mul_assoc, (Sp.idem i₀).eq, mul_smul,
    Sp.e_smul_coe]

def actP : Sp.CornerRing i₀ →ₐ[𝒪] Module.End 𝒪 ℙ := Algebra.lsmul 𝒪 𝒪 _

theorem actP_apply (z : Sp.CornerRing i₀) (y : ℙ) : actP N S r 𝒪 θ hc₀ Sp i₀ z y = z • y := rfl

theorem actP_injective : Function.Injective (actP N S r 𝒪 θ hc₀ Sp i₀) := by
  intro z w h
  refine cornerSmul_injective (V := 𝕍) (fun b b' hb => ?_) Sp i₀ z w fun y => ?_
  · exact Subtype.ext (LinearMap.ext hb)
  · exact LinearMap.congr_fun h y

end Concrete

end EscompES
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_exists_algHom_moduleEnd_baseML_injective.EscompES"

end
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_exists_algHom_moduleEnd_baseML_injective.EscompES"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
open EscompES IharaLemma CuspForm.AuxLevel in
open scoped IsMulCommutative in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hpS : p ∈ S)
    (N : ℕ) [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (r : ℕ)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (hc₀ : CuspForm.AuxLevel.BaseOpComm N r (↑S : Set ℕ) 𝒪) :
    ∃ ι : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪]
        Module.End 𝒪 (CuspForm.AuxLevel.baseML N r (↑S : Set ℕ) 𝒪 θ hc₀),
      Function.Injective ι ∧
      ∀ (g : CuspForm.AuxLevel.Gen N r (↑S : Set ℕ))
        (m : CuspForm.AuxLevel.baseML N r (↑S : Set ℕ) 𝒪 θ hc₀),
        ι (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ
            (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem)) m =
          (MvPolynomial.X g : (CuspForm.AuxLevel.baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).FreeAlg) •
            m := by
  classical

  set S' : Finset ℕ := insert r S with hS'def
  have hSS' : S ⊆ S' := Finset.subset_insert r S
  have hmono : CuspForm.heckeAlgebra N 2 (↑S' : Set ℕ) ≤ CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) :=
    CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hSS')
  let incl : CuspForm.heckeAlgebra N 2 (↑S' : Set ℕ) →ₐ[ℤ] CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) :=
    Subalgebra.inclusion hmono
  let θ' : CuspForm.heckeAlgebra N 2 (↑S' : Set ℕ) →+* ResidueField 𝒪 := θ.comp incl.toRingHom
  have hθ' : ∀ t : CuspForm.heckeAlgebra N 2 (↑S' : Set ℕ),
      θ' t = θ (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hSS')) t) :=
    fun _ => rfl
  obtain ⟨Ψ, -, hΨ⟩ := CuspForm.heckeLocal.exists_algHom_of_subset N (↑S' : Set ℕ) (↑S : Set ℕ)
    (Finset.coe_subset.mpr hSS') 𝒪 θ θ' hθ'
  have hΨbij : Function.Bijective Ψ :=
    CuspForm.heckeLocal.bijective_of_subset_of_forall_prime_mem_of_charpoly_frobenius_eq p hp𝒪 ρbar
      habs S' S hpS hSS' N hNS θ hθ θ' hθ' Ψ hΨ
  let Ψe : CuspForm.heckeLocal N (↑S' : Set ℕ) 𝒪 θ' ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ :=
    AlgEquiv.ofBijective Ψ hΨbij
  have hΨe_gen : ∀ g : Gen N r (↑S : Set ℕ),
      Ψe.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ
        (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem)) =
      CuspForm.heckeLocal.π N (↑S' : Set ℕ) 𝒪 θ'
        (CuspForm.heckeAlgebra.T g.prime g.not_dvd
          (fun h => (Finset.mem_insert.mp h).elim g.ne g.notMem)) := by
    intro g
    apply Ψe.injective
    rw [AlgEquiv.apply_symm_apply]
    show _ = Ψ _
    rw [hΨ]
    rfl

  have hEis := exists_nonEis_prime ρbar habs S N r θ hθ

  haveI : Module.Finite 𝒪 (CohCarrier.H1 N ⊤ 𝒪) := CohCarrier.H1_moduleFinite N ⊤ 𝒪 𝒪
  obtain ⟨Sp⟩ := CohCarrier.HeckeData.nonempty_idempotentSplitting_opSubalgebra
    (baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀)
  obtain ⟨i₀, πk, hπk, E, hE⟩ :=
    CuspForm.heckeLocal.exists_algEquiv_cornerRing_baseHeckeData_of_not_isEisenstein N S hNS r 𝒪 θ θ'
      hθ' hc₀ hEis Sp

  letI := modP N S r 𝒪 θ hc₀ Sp i₀
  obtain ⟨Φ, -⟩ := exists_linearEquiv_baseML_corner N S r 𝒪 θ hc₀ Sp i₀ πk hπk
  let Φₒ : baseML N r (↑S : Set ℕ) 𝒪 θ hc₀ ≃ₗ[𝒪]
      ↥(cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) := Φ.restrictScalars 𝒪

  let conj : Module.End 𝒪 ↥(cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) ≃ₐ[𝒪]
      Module.End 𝒪 (baseML N r (↑S : Set ℕ) 𝒪 θ hc₀) := LinearEquiv.conjAlgEquiv 𝒪 Φₒ.symm
  let ι : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪]
      Module.End 𝒪 (baseML N r (↑S : Set ℕ) 𝒪 θ hc₀) :=
    conj.toAlgHom.comp ((actP N S r 𝒪 θ hc₀ Sp i₀).comp
      (E.toAlgHom.comp Ψe.symm.toAlgHom))
  refine ⟨ι, ?_, fun g m => ?_⟩
  ·
    exact conj.injective.comp ((actP_injective N S r 𝒪 θ hc₀ Sp i₀).comp
      (E.injective.comp Ψe.symm.injective))
  ·
    show conj (actP N S r 𝒪 θ hc₀ Sp i₀ (E (Ψe.symm _))) m = _
    rw [hΨe_gen, hE, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_symm, actP_apply, cornerT_smul]
    show Φₒ.symm ((MvPolynomial.X g : (baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).FreeAlg) • Φ m) = _
    rw [← map_smul Φ]
    exact Φ.symm_apply_apply _

end S_CuspForm_heckeLocal_exists_algHom_moduleEnd_baseML_injective
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_algHom_moduleEnd_baseML_injective (solution)

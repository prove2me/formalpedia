-- Prove2me | solution 1 for CuspForm.heckeLocal.finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b238a883-1752-572f-8cea-12ad7c8299b5

import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Theorems.Thm_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul
import Theorems.Thm_CohCarrier_eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms
import Theorems.Thm_CohCarrier_heckeT_iDeg_interchange
import Theorems.Thm_CohCarrier_heckeT_iDeg_q_eq_smul
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_iDeg_comp
import Theorems.Thm_CohCarrier_injective_iDeg_one_and_range_eq_of_isUnit_index
import Theorems.Thm_CohCarrier_mem_map_iDegL_one_parabolicHoms_iff
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
import Theorems.Thm_CohCarrier_heckeT_mem_parabolicHoms
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_CuspForm_heckeLocal_exists_algHom_of_subset
import Theorems.Thm_CuspForm_heckeLocal_bijective_of_subset_of_forall_prime_mem_of_charpoly_frobenius_eq
import Theorems.Thm_CuspForm_heckeLocal_adjoin_range_pi
import Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Theorems.Thm_IsLocalRing_residue_algHom_apply_eq_of_residue_eq_map
import Theorems.Thm_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 Ihara.instGroupIharaAmalgam FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow Deformation.ProartinianCat.instCategory Deformation.ProartinianCat.topologicalSpace Deformation.ProartinianCat.instUniqueHomSelf Deformation.IsLocalProartinianAlgebra.toIsLocalHom Deformation.ProartinianCat.instDiscreteTopologyCarrierResidueField Deformation.ProartinianCat.algebra Deformation.IsLocalProartinianAlgebra.toIsLocalRing Deformation.IsLocalProartinianAlgebra.toIsProartinian Deformation.IsLocalProartinianAlgebra.toIsTopologicalRing Deformation.ProartinianCat.instCoeSortType Deformation.ProartinianCat.instUniqueHomResidueField Deformation.ProartinianCat.instIsLocalHomCarrierContinuousAlgHomHom Deformation.IsLocalProartinianAlgebra.toIsResidueAlgebra Deformation.ProartinianCat.isLocalProartinianAlgebra Deformation.ProartinianCat.instIsAdicTopologyCarrierSelf Deformation.ProartinianCat.commRing"
p2m_attr_erase "instance" "Deformation.ProartinianCat.instFieldCarrierResidueField IsLocalRing.instDiscreteTopologyQuotientIdealHPowNatMaximalIdeal_definitions IsLocalRing.instIsLinearTopology_definitions IsProartinian.toT0Space instIsProartinianOfDiscreteTopologyOfIsArtinianRing IsLocalRing.instIsAdicTopology instIsProartinianOfIsAdicTopologyOfIsNoetherianRingOfCompactSpace IsLocalRing.instIsHausdorffMaximalIdealOfIsNoetherianRing_definitions IsLocalRing.instNonarchimedeanRing_definitions IsLocalRing.instIsPrecompleteMaximalIdealOfCompactSpace_definitions IsLocalRing.instDiscreteTopologyOfIsArtinianRing_definitions IsLocalRing.instT2SpaceOfIsNoetherianRing_definitions IsProartinian.toCompleteSpace IsProartinian.toIsLinearTopology instTopologicallyFGOfFiniteType instMulSemiringActionSubtypeMemIntermediateFieldOfSMulCommClassOfNormal_definitions instIsLocalHomRingHomAlgebraMap_definitions instContinuousConstSMulConjActOfContinuousMul_definitions instIsLocalHomRingHomToRingHom_definitions_1 instIsLocalHomResidueFieldRingHomAlgebraMap_definitions instMulSemiringActionRingOfIntegers_definitions instIsLocalHomRingHomToRingHom_definitions instMulActionContinuousMonoidHomOfContinuousConstSMul_definitions instFiniteIndexMulOppositeOp_definitions ValuationSubring.smulCommClass instFaithfulSMulSubtypeMemValuationSubring_definitions ContinuousAlgHom.isLocalHom_id instIsModuleTopologyMatrixOfFiniteOfIsTopologicalRing_definitions IsTopologicalAddGroup.discreteUniformity IntermediateField.smulCommClass_of_normal instMulActionMonoidHomOfMulDistribMulAction_definitions IsTopologicalGroup.discreteUniformity instIsLocalHomRingHomOfContinuousAlgHom_definitions Additive.instDistrbMulAction instIsLocalHomRingHomOfContinuousAlgHom_definitions_1 instNumberFieldSubtypeMemIntermediateFieldOfFiniteDimensional_definitions ContinuousAlgHom.isLocalHom_comp instIsLocalHomContinuousAlgHomToContinuousAlgHom_definitions IsResidueAlgebra.inst IsResidueAlgebra.instQuotientIdeal"
p2m_attr_erase "instance" "IsLocalRing.quot IsLocalHom.quotient_mk Deformation.ProartinianCat.ClosedSubalgebra.instNontrivialSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsLinearTopologySubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsTopologicalRingSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace TateModule.instModule TateModule.instSMul AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec Deformation.ProartinianCat.Hom.mk.injEq Deformation.ProartinianCat.ofHom_comp Deformation.ProartinianCat.hom_comp Deformation.ProartinianCat.mk.sizeOf_spec Deformation.ProartinianCat.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "Deformation.ProartinianCat.ofEquiv_hom_hom Deformation.ProartinianCat.ofHom_id Deformation.ProartinianCat.hom_id Deformation.ProartinianCat.ofEquiv_inv_hom Deformation.ProartinianCat.mk.injEq Deformation.ProartinianCat.ofHom_hom ContinuousMonoidHom.val_inv_toHomUnits_toFun Units.val_mapₜ_toFun MonoidHom.coe_smul ContinuousAlgHom.coe_toContinuousMonoidHom ContinuousMonoidHom.val_toHomUnits_toFun ContinuousMonoidHom.mk_toMonoidHom ContinuousAlgHom.mapMatrix_apply Units.val_inv_mapₜ_toFun Units.coeHomₜ_toFun ContinuousMonoidHom.coe_mk ContinuousMonoidHom.coe_smul Deformation.repnFunctor_map Deformation.mapRepn_apply Deformation.ProartinianCat.closedSubalgebraι_apply Deformation.matrixRepresentation_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "Gen heckeTL diamondL opFamily Gen.T Gen.dia Gen.U coresAdd gamma0Units GammaH mem_GammaH_iff H1 conjL heckeT diamondRaw LevelLE iDeg' iDegL exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms heckeT_iDeg_interchange heckeT_iDeg_q_eq_smul iDeg_heckeT_comm_of_coprime iDeg_heckeT_comm_of_dvd injective_iDeg_one_and_range_eq_of_isUnit_index mem_map_iDegL_one_parabolicHoms_iff heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one heckeT_mem_parabolicHoms heckeTlower"
p2m_open "CohCarrier"

open CongruenceSubgroup

section FiniteIndex

variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ)

theorem Gamma_le_GammaH : Gamma M ≤ GammaH M Hs := by
  intro A hA
  rw [mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    simp [gamma0Units, Gamma0Map, hA'.2.2.2]
  rw [this]; exact one_mem _

scoped instance GammaH_finiteIndex [NeZero M] : (GammaH M Hs).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M Hs)

end FiniteIndex

section Transfer

variable {G : Type*} [Group G] {K : Subgroup G} {C C' : Type*} [CommGroup C] [CommGroup C']

open Subgroup Subgroup.leftTransversals in
theorem transfer_comp [K.FiniteIndex] (ψ : C →* C') (ϕ : K →* C) :
    MonoidHom.transfer (ψ.comp ϕ) = ψ.comp (MonoidHom.transfer ϕ) := by
  ext g
  rw [MonoidHom.comp_apply, MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default]
  simp only [diff, map_prod, MonoidHom.comp_apply]

theorem coresAdd_comp_left (Ksub : Subgroup G) [Ksub.FiniteIndex] {B B' : Type*} [AddCommGroup B] [AddCommGroup B']
    (f : B →+ B') (φ : Additive ↥Ksub →+ B) :
    coresAdd Ksub (f.comp φ) = f.comp (coresAdd Ksub φ) := by
  have h1 : AddMonoidHom.toMultiplicativeRight (f.comp φ) =
      (AddMonoidHom.toMultiplicative f).comp (AddMonoidHom.toMultiplicativeRight φ) := by
    ext; rfl
  simp only [coresAdd, h1, transfer_comp]
  ext; rfl

end Transfer

section Coeff

variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ) {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def mapCoeff (f : A →+ B) : H1 M Hs A →+ H1 M Hs B := AddMonoidHom.compHom f

@[scoped simp] theorem mapCoeff_apply (f : A →+ B) (φ : H1 M Hs A) : mapCoeff M Hs f φ = f.comp φ := rfl

theorem mapCoeff_injective (f : A →+ B) (hf : Function.Injective f) :
    Function.Injective (mapCoeff M Hs f) := by
  intro φ ψ h
  ext g
  exact hf (DFunLike.congr_fun h g)

theorem heckeT_mapCoeff (ℓ : ℕ) [NeZero ℓ] (f : A →+ B) (φ : H1 M Hs A) :
    heckeT M Hs ℓ B (f.comp φ) = f.comp (heckeT M Hs ℓ A φ) := by
  have h1 : (AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL M Hs ℓ) =
      (AddMonoidHom.toMultiplicative f).comp
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M Hs ℓ)) := by
    ext; rfl
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp
      (conjL M Hs ℓ))) = f.comp (MonoidHom.toAdditiveLeft (MonoidHom.transfer
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M Hs ℓ))))
  rw [h1, transfer_comp]
  ext; rfl

theorem iDeg'_mapCoeff {M' d : ℕ} {Hs' : Subgroup (ZMod M')ˣ} [NeZero d] (h : LevelLE M M' Hs Hs' d)
    (f : A →+ B) (φ : H1 M Hs A) :
    iDeg' M M' Hs Hs' d B h (f.comp φ) = f.comp (iDeg' M M' Hs Hs' d A h φ) := rfl

theorem diamondRaw_mapCoeff (σ : Gamma0 M) (f : A →+ B) (φ : H1 M Hs A) :
    diamondRaw M Hs B σ (f.comp φ) = f.comp (diamondRaw M Hs A σ φ) := rfl

theorem isParabolicHom_comp {f : A →+ B} {φ : H1 M Hs A}
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) (f.comp φ) := by
  intro γ hγ
  simp [hφ γ hγ]

theorem isParabolicHom_of_comp {f : A →+ B} (hf : Function.Injective f) {φ : H1 M Hs A}
    (hφ : ModularCurve.Period.IsParabolicHom (GammaH M Hs) (f.comp φ)) :
    ModularCurve.Period.IsParabolicHom (GammaH M Hs) φ := by
  intro γ hγ
  apply hf
  simpa using hφ γ hγ

theorem mem_parabolicHoms_iff_int {R : Type*} [Semiring R] [Module R A] {Γ : Subgroup SL(2, ℤ)}
    (φ : Additive ↥Γ →+ A) :
    φ ∈ ModularCurve.Period.parabolicHoms R Γ A ↔ φ ∈ ModularCurve.Period.parabolicHoms ℤ Γ A := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff, ModularCurve.Period.mem_parabolicHoms_iff]

end Coeff

section Cast

variable (𝒪 : Type) [CommRing 𝒪] (K : Type) [CommRing K] [Algebra 𝒪 K]
variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ)

def castL : H1 M Hs 𝒪 →ₗ[𝒪] H1 M Hs K where
  toFun φ := (algebraMap 𝒪 K).toAddMonoidHom.comp φ
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by ext; simp [Algebra.smul_def]

@[scoped simp] theorem castL_apply (φ : H1 M Hs 𝒪) : castL 𝒪 K M Hs φ = (algebraMap 𝒪 K).toAddMonoidHom.comp φ := rfl

theorem castL_injective (hinj : Function.Injective (algebraMap 𝒪 K)) :
    Function.Injective (castL 𝒪 K M Hs) :=
  mapCoeff_injective M Hs _ hinj

theorem castL_smul' (c : 𝒪) (φ : H1 M Hs 𝒪) :
    castL 𝒪 K M Hs (c • φ) = algebraMap 𝒪 K c • castL 𝒪 K M Hs φ := by
  rw [LinearMap.map_smul, algebraMap_smul]

theorem heckeT_castL (ℓ : ℕ) [NeZero ℓ] (φ : H1 M Hs 𝒪) :
    heckeT M Hs ℓ K (castL 𝒪 K M Hs φ) = castL 𝒪 K M Hs (heckeT M Hs ℓ 𝒪 φ) :=
  heckeT_mapCoeff M Hs ℓ _ φ

theorem iDegL_castL {M' d : ℕ} {Hs' : Subgroup (ZMod M')ˣ} [NeZero d] (h : LevelLE M M' Hs Hs' d)
    (φ : H1 M Hs 𝒪) :
    iDegL M M' Hs Hs' d K K h (castL 𝒪 K M Hs φ) = castL 𝒪 K M' Hs' (iDegL M M' Hs Hs' d 𝒪 𝒪 h φ) := rfl

theorem diamondRaw_castL (σ : Gamma0 M) (φ : H1 M Hs 𝒪) :
    diamondRaw M Hs K σ (castL 𝒪 K M Hs φ) = castL 𝒪 K M Hs (diamondRaw M Hs 𝒪 σ φ) := rfl

theorem heckeT_smul' {R : Type} [CommRing R] (ℓ : ℕ) [NeZero ℓ] (c : R) (φ : H1 M Hs R) :
    heckeT M Hs ℓ R (c • φ) = c • heckeT M Hs ℓ R φ :=
  (heckeTL M Hs R ℓ).map_smul c φ

theorem diamondRaw_smul' {A : Type*} [AddCommGroup A] {R : Type*} [Semiring R] [Module R A]
    (σ : Gamma0 M) (c : R) (φ : H1 M Hs A) :
    diamondRaw M Hs A σ (c • φ) = c • diamondRaw M Hs A σ φ := rfl

theorem iDegL_eq_iDeg' {A : Type*} [AddCommGroup A] (R : Type*) [Semiring R] [Module R A]
    {M' d : ℕ} {Hs' : Subgroup (ZMod M')ˣ} [NeZero d] (h : LevelLE M M' Hs Hs' d) (φ : H1 M Hs A) :
    iDegL M M' Hs Hs' d A R h φ = iDeg' M M' Hs Hs' d A h φ := rfl

end Cast

section TorsionFree

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] (M : ℕ) (Hs : Subgroup (ZMod M)ˣ)

scoped instance : NoZeroSMulDivisors 𝒪 (H1 M Hs 𝒪) := by
  refine ⟨fun {c φ} h => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    refine AddMonoidHom.ext fun x => ?_
    have h' : c * φ x = 0 := DFunLike.congr_fun h x
    exact (mul_eq_zero.mp h').resolve_left hc

end TorsionFree

end CohCarrier
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.CohCarrier"

section RankLemma

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]
  {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

namespace Module p2m_export "Module" "Injective Free.chooseBasis finrank Free compHom restrictScalars finrank_eq_card_chooseBasisIndex" end Module
p2m_open_scoped "Module" in

theorem Module.finrank_le_finrank_of_injective_of_isFractionRing
    {E : Type*} [AddCommGroup E] [Module 𝒪 E] [Module.Finite 𝒪 E] [Module.Free 𝒪 E]
    {W : Type*} [AddCommGroup W] [Module K W] [Module 𝒪 W] [IsScalarTower 𝒪 K W]
    [FiniteDimensional K W]
    (f : E →ₗ[𝒪] W) (hf : Function.Injective f) :
    Module.finrank 𝒪 E ≤ Module.finrank K W := by
  classical
  let b := Module.Free.chooseBasis 𝒪 E

  have hli : LinearIndependent K (fun i => f (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i

    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors 𝒪)
      (Finset.univ.image g)
    have hc' : ∀ j, IsLocalization.IsInteger 𝒪 ((c : 𝒪) • g j) := fun j =>
      hc (g j) (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    choose d hd using hc'
    have hsum : f (∑ j, d j • b j) = 0 := by
      rw [map_sum]
      have : ∀ j, f (d j • b j) = ((c : 𝒪) • g j) • f (b j) := by
        intro j
        rw [LinearMap.map_smul, ← hd j, algebraMap_smul]
      simp_rw [this, smul_assoc, ← Finset.smul_sum, hg, smul_zero]
    have hzero : ∑ j, d j • b j = 0 := hf (by rw [hsum, map_zero])
    have hd0 : d i = 0 := by
      have := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at this
      exact this d hzero i
    have hcg : (c : 𝒪) • g i = 0 := by
      have h := hd i
      rw [hd0, map_zero] at h
      exact h.symm
    rw [Algebra.smul_def] at hcg
    rcases mul_eq_zero.mp hcg with h | h
    · exact absurd h (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2)
    · exact h
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_eq_card_chooseBasisIndex]
  convert this

p2m_open_scoped "Module" in

theorem Module.finrank_le_of_forall_exists_smul_eq_of_isFractionRing
    {E₁ : Type*} [AddCommGroup E₁] [Module 𝒪 E₁] [Module.Finite 𝒪 E₁] [Module.Free 𝒪 E₁]
    {W : Type*} [AddCommGroup W] [Module K W] [Module 𝒪 W] [IsScalarTower 𝒪 K W]
    {V₀ : Type*} [AddCommGroup V₀] [Module 𝒪 V₀]
    (Φ : E₁ →ₗ[𝒪] W) (hΦ : Function.Injective Φ)
    (E₀ : Submodule 𝒪 V₀) [Module.Finite 𝒪 E₀] [Module.Free 𝒪 E₀] (c₀ : V₀ →ₗ[𝒪] W)
    (h : ∀ x, ∃ c : 𝒪, c ≠ 0 ∧ ∃ m ∈ E₀, c₀ m = algebraMap 𝒪 K c • Φ x) :
    Module.finrank 𝒪 E₁ ≤ Module.finrank 𝒪 E₀ := by
  classical
  have hinj : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  let bE := Module.Free.chooseBasis 𝒪 E₀
  let W₀ : Submodule K W := Submodule.span K (Set.range fun i => c₀ (bE i : V₀))
  haveI : FiniteDimensional K W₀ := FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hW₀rank : Module.finrank K W₀ ≤ Module.finrank 𝒪 E₀ := by
    rw [Module.finrank_eq_card_chooseBasisIndex 𝒪 E₀]
    exact finrank_range_le_card _
  have hcast : ∀ m ∈ E₀, c₀ m ∈ W₀ := by
    intro m hm
    have hsum : (⟨m, hm⟩ : E₀) = ∑ i, bE.repr ⟨m, hm⟩ i • bE i := (bE.sum_repr ⟨m, hm⟩).symm
    have hm' : c₀ m = ∑ i, bE.repr ⟨m, hm⟩ i • c₀ (bE i : V₀) := by
      have := congrArg (c₀ ∘ₗ E₀.subtype) hsum
      rw [map_sum] at this
      simpa only [LinearMap.comp_apply, Submodule.subtype_apply, map_smul] using this
    rw [hm']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hmem : ∀ x, Φ x ∈ W₀ := by
    intro x
    obtain ⟨c, hc, m, hmE, hm⟩ := h x
    have hc' : algebraMap 𝒪 K c ≠ 0 := fun h0 => hc (hinj (by rw [h0, map_zero]))
    have : Φ x = (algebraMap 𝒪 K c)⁻¹ • c₀ m := by
      rw [hm, smul_smul, inv_mul_cancel₀ hc', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (hcast m hmE)
  let Φ' : E₁ →ₗ[𝒪] W₀ :=
    { toFun := fun x => ⟨Φ x, hmem x⟩
      map_add' := fun x y => Subtype.ext (map_add Φ x y)
      map_smul' := fun c x => Subtype.ext (by
        simp only [RingHom.id_apply, Submodule.coe_smul_of_tower, LinearMap.map_smul]) }
  have hΦ' : Function.Injective Φ' := fun x y hxy =>
    hΦ (congrArg (fun z : W₀ => (z : W)) hxy)
  calc Module.finrank 𝒪 E₁ ≤ Module.finrank K W₀ :=
        Module.finrank_le_finrank_of_injective_of_isFractionRing Φ' hΦ'
    _ ≤ Module.finrank 𝒪 E₀ := hW₀rank

end RankLemma
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.CohCarrier"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CohCarrier P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.CohCarrier CongruenceSubgroup ModularCurve.Period"

namespace Rg6

section Core

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [CharZero 𝒪]

theorem finrank_le_of_eigen_data
    (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero (N * r)] [NeZero (N * r * p)]
    (hpNr : ¬ p ∣ N * r)
    (S : Finset ℕ) (hpS : p ∈ S)
    (H₀ : Subgroup (ZMod (N * r))ˣ) (H : Subgroup (ZMod (N * r * p))ˣ)
    (h1 : LevelLE (N * r) (N * r * p) H₀ H 1) (hp' : LevelLE (N * r) (N * r * p) H₀ H p)
    (h₁ₐ : LevelLE (N * r * p) (N * r * p) ⊤ H 1)
    (h1t : LevelLE (N * r) (N * r * p) ⊤ ⊤ 1) (hpt : LevelLE (N * r) (N * r * p) ⊤ ⊤ p)
    (h₀ : LevelLE (N * r) (N * r) ⊤ H₀ 1)
    (a : ℕ → 𝒪) (u : 𝒪) (hu : u ≠ 0) (cq : ℕ → 𝒪)
    (ℓ₁ : ℕ) [NeZero ℓ₁] (hℓ₁ : ℓ₁.Prime) (hℓ₁S : ℓ₁ ∉ S) (hℓ₁N : ¬ ℓ₁ ∣ N * r * p) (hℓ₁mod : ℓ₁ ≡ 1 [MOD N * r])
    (hℓ₁unit : IsUnit (a ℓ₁ - ((ℓ₁ : 𝒪) + 1)))
    (E1 : Submodule 𝒪 (H1 (N * r * p) H 𝒪)) [Module.Finite 𝒪 E1]
    (hE1par : ∀ v ∈ E1, v ∈ (parabolicHoms 𝒪 (GammaH (N * r * p) ⊤) 𝒪).map
      (iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ))
    (hE1T : ∀ v ∈ E1, ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r * p) H ℓ 𝒪 v = a ℓ • v)
    (hE1U : ∀ v ∈ E1, heckeT (N * r * p) H p 𝒪 v = u • v)
    (hE1q : ∀ v ∈ E1, ∀ (q : ℕ) [NeZero q], q.Prime → q ∣ N → heckeT (N * r * p) H q 𝒪 v = cq q • v)
    (E0 : Submodule 𝒪 (H1 (N * r) H₀ 𝒪)) [Module.Finite 𝒪 E0]
    (hE0ne : E0 ≠ ⊥)
    (hE0T : ∀ m ∈ E0, ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r) H₀ ℓ 𝒪 m = a ℓ • m)
    (hE0dia : ∀ m ∈ E0, ∀ σ : Gamma0 (N * r), diamondRaw (N * r) H₀ 𝒪 σ m = m)
    (hE0mem : ∀ m : H1 (N * r) H₀ 𝒪,
      (∀ σ : Gamma0 (N * r), diamondRaw (N * r) H₀ 𝒪 σ m = m) →
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r → heckeT (N * r) H₀ ℓ 𝒪 m = a ℓ • m) →
      (∀ (q : ℕ) [NeZero q], q.Prime → q ∣ N → heckeT (N * r) H₀ q 𝒪 m = cq q • m) → m ∈ E0) :
    Module.finrank 𝒪 E1 ≤ Module.finrank 𝒪 E0 := by
  classical
  let K := FractionRing 𝒪
  have hinjOK : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
  haveI : CharZero K := charZero_of_injective_algebraMap hinjOK
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  set cK1 := castL 𝒪 K (N * r * p) H with hcK1
  set cK1t := castL 𝒪 K (N * r * p) ⊤ with hcK1t
  set cK0 := castL 𝒪 K (N * r) H₀ with hcK0
  set cK0t := castL 𝒪 K (N * r) ⊤ with hcK0t

  set res' := iDegL (N * r * p) (N * r * p) ⊤ H 1 K K h₁ₐ with hres'
  set res₀ := iDegL (N * r) (N * r) ⊤ H₀ 1 K K h₀ with hres₀
  set ι₁ := iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t with hι₁
  set ιp := iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt with hιp

  have hcK1inj : Function.Injective (castL 𝒪 K (N * r * p) H) := castL_injective 𝒪 K _ _ hinjOK
  have hcK1tinj : Function.Injective (castL 𝒪 K (N * r * p) ⊤) := castL_injective 𝒪 K _ _ hinjOK
  have hcK0inj : Function.Injective (castL 𝒪 K (N * r) H₀) := castL_injective 𝒪 K _ _ hinjOK
  have hcK0tinj : Function.Injective (castL 𝒪 K (N * r) ⊤) := castL_injective 𝒪 K _ _ hinjOK

  have hunitH : IsUnit ((H.index : ℕ) : K) := by
    have : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast this)
  have hunitH₀ : IsUnit ((H₀.index : ℕ) : K) := by
    have : H₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast this)
  have hres'inj : Function.Injective (iDegL (N * r * p) (N * r * p) ⊤ H 1 K K h₁ₐ) :=
    (injective_iDeg_one_and_range_eq_of_isUnit_index (N * r * p) H K K h₁ₐ hunitH).2.1
  have hres₀inj : Function.Injective (iDegL (N * r) (N * r) ⊤ H₀ 1 K K h₀) :=
    (injective_iDeg_one_and_range_eq_of_isUnit_index (N * r) H₀ K K h₀ hunitH₀).2.1
  have hres₀range := (injective_iDeg_one_and_range_eq_of_isUnit_index (N * r) H₀ K K h₀ hunitH₀).2.2.1

  have hres'𝒪inj : Function.Injective (iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ) := by
    intro w w' hww'
    apply hcK1tinj
    apply hres'inj
    have := congrArg (castL 𝒪 K (N * r * p) H) hww'
    rwa [← iDegL_castL, ← iDegL_castL] at this

  have cast_smul : ∀ (M' : ℕ) (H' : Subgroup (ZMod M')ˣ) (c : 𝒪) (φ : H1 M' H' 𝒪),
      castL 𝒪 K M' H' (c • φ) = algebraMap 𝒪 K c • castL 𝒪 K M' H' φ := by
    intro M' H' c φ
    rw [LinearMap.map_smul, algebraMap_smul]

  obtain ⟨m₀, hm₀E, hm₀ne⟩ := (Submodule.ne_bot_iff E0).mp hE0ne
  have hm₀K_ne : castL 𝒪 K (N * r) H₀ m₀ ≠ 0 := fun h => hm₀ne (hcK0inj (by rw [h, map_zero]))
  have hm₀K_dia : ∀ σ : Gamma0 (N * r),
      diamondRaw (N * r) H₀ K σ (castL 𝒪 K (N * r) H₀ m₀) = castL 𝒪 K (N * r) H₀ m₀ := by
    intro σ
    rw [diamondRaw_castL, hE0dia m₀ hm₀E σ]
  have hm₀K_T : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r) H₀ ℓ K (castL 𝒪 K (N * r) H₀ m₀) =
        algebraMap 𝒪 K (a ℓ) • castL 𝒪 K (N * r) H₀ m₀ := by
    intro ℓ _ hℓ hℓS hℓN
    rw [heckeT_castL, hE0T m₀ hm₀E ℓ hℓ hℓS hℓN, cast_smul]
  have hℓ₁Nr : ¬ ℓ₁ ∣ N * r := fun h => hℓ₁N (h.mul_right p)
  have hm₀K_par : castL 𝒪 K (N * r) H₀ m₀ ∈ parabolicHoms K (GammaH (N * r) H₀) K := by
    have hmem := heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one (N * r) H₀ K
      (castL 𝒪 K (N * r) H₀ m₀) ℓ₁ hℓ₁ hℓ₁Nr hℓ₁mod
    rw [hm₀K_T ℓ₁ hℓ₁ hℓ₁S hℓ₁N] at hmem
    have hcoef : algebraMap 𝒪 K (a ℓ₁) • castL 𝒪 K (N * r) H₀ m₀ - (ℓ₁ + 1) • castL 𝒪 K (N * r) H₀ m₀ =
        algebraMap 𝒪 K (a ℓ₁ - ((ℓ₁ : 𝒪) + 1)) • castL 𝒪 K (N * r) H₀ m₀ := by
      rw [map_sub, sub_smul, map_add, map_one, map_natCast, ← Nat.cast_smul_eq_nsmul K]
      push_cast
      rfl
    rw [hcoef] at hmem
    obtain ⟨w, hw⟩ := hℓ₁unit
    have hne : algebraMap 𝒪 K (a ℓ₁ - ((ℓ₁ : 𝒪) + 1)) ≠ 0 := by
      rw [← hw]; exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero w.ne_zero)
    rw [mem_parabolicHoms_iff] at hmem ⊢
    intro γ hγ
    have := hmem γ hγ
    rw [AddMonoidHom.smul_apply, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left hne
  obtain ⟨x₀, hx₀par, hx₀eq⟩ := Submodule.mem_map.mp
    ((mem_map_iDegL_one_parabolicHoms_iff (N * r) H₀ K K h₀ hunitH₀ _).mpr ⟨hm₀K_par, hm₀K_dia⟩)
  have hx₀ne : x₀ ≠ 0 := by
    rintro rfl
    exact hm₀K_ne (by rw [← hx₀eq, map_zero])
  have hx₀T : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r) ⊤ ℓ K x₀ = algebraMap 𝒪 K (a ℓ) • x₀ := by
    intro ℓ _ hℓ hℓS hℓN
    apply hres₀inj
    have hℓNr : ¬ ℓ ∣ N * r := fun h => hℓN (h.mul_right p)
    have hc := iDeg_heckeT_comm_of_coprime (A := K) h₀ (Nat.coprime_one_right ℓ) hℓ hℓNr x₀
    rw [LinearMap.map_smul]
    show iDeg' (N * r) (N * r) ⊤ H₀ 1 K h₀ (heckeT (N * r) ⊤ ℓ K x₀) = _
    rw [hc]
    show heckeT (N * r) H₀ ℓ K (iDegL (N * r) (N * r) ⊤ H₀ 1 K K h₀ x₀) = _
    rw [hx₀eq, hm₀K_T ℓ hℓ hℓS hℓN]

  have hex : ∀ x : E1, ∃ w : H1 (N * r * p) ⊤ 𝒪, w ∈ parabolicHoms 𝒪 (GammaH (N * r * p) ⊤) 𝒪 ∧
      iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ w = (x : H1 (N * r * p) H 𝒪) := fun x =>
    Submodule.mem_map.mp (hE1par x x.2)
  choose L hLpar hLeq using hex
  have hLadd : ∀ x y : E1, L (x + y) = L x + L y := fun x y =>
    hres'𝒪inj (by rw [map_add, hLeq, hLeq, hLeq]; rfl)
  have hLsmul : ∀ (c : 𝒪) (x : E1), L (c • x) = c • L x := fun c x =>
    hres'𝒪inj (by rw [LinearMap.map_smul, hLeq, hLeq]; rfl)

  have hLT : ∀ (x : E1) (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r * p) ⊤ ℓ 𝒪 (L x) = a ℓ • L x := by
    intro x ℓ _ hℓ hℓS hℓN
    apply hres'𝒪inj
    have hc := iDeg_heckeT_comm_of_coprime (A := 𝒪) h₁ₐ (Nat.coprime_one_right ℓ) hℓ hℓN (L x)
    rw [LinearMap.map_smul]
    show iDeg' _ _ ⊤ H 1 𝒪 h₁ₐ (heckeT (N * r * p) ⊤ ℓ 𝒪 (L x)) = _
    rw [hc]
    show heckeT (N * r * p) H ℓ 𝒪 (iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ (L x)) = _
    rw [hLeq, hE1T x x.2 ℓ hℓ hℓS hℓN]
  have hLU : ∀ x : E1, heckeT (N * r * p) ⊤ p 𝒪 (L x) = u • L x := by
    intro x
    apply hres'𝒪inj
    have hc := iDeg_heckeT_comm_of_dvd (A := 𝒪) h₁ₐ (Nat.coprime_one_right p) (dvd_mul_left p (N * r)) (L x)
    rw [LinearMap.map_smul]
    show iDeg' _ _ ⊤ H 1 𝒪 h₁ₐ (heckeT (N * r * p) ⊤ p 𝒪 (L x)) = _
    rw [hc]
    show heckeT (N * r * p) H p 𝒪 (iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ (L x)) = _
    rw [hLeq, hE1U x x.2]
  have hLq : ∀ (x : E1) (q : ℕ) [NeZero q], q.Prime → q ∣ N →
      heckeT (N * r * p) ⊤ q 𝒪 (L x) = cq q • L x := by
    intro x q _ hq hqN
    apply hres'𝒪inj
    have hqd : q ∣ N * r * p := (hqN.mul_right r).mul_right p
    have hc := iDeg_heckeT_comm_of_dvd (A := 𝒪) h₁ₐ (Nat.coprime_one_right q) hqd (L x)
    rw [LinearMap.map_smul]
    show iDeg' _ _ ⊤ H 1 𝒪 h₁ₐ (heckeT (N * r * p) ⊤ q 𝒪 (L x)) = _
    rw [hc]
    show heckeT (N * r * p) H q 𝒪 (iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ (L x)) = _
    rw [hLeq, hE1q x x.2 q hq hqN]

  set wK : E1 → H1 (N * r * p) ⊤ K := fun x => castL 𝒪 K (N * r * p) ⊤ (L x) with hwK
  have hwKpar : ∀ x, wK x ∈ parabolicHoms K (GammaH (N * r * p) ⊤) K := fun x => by
    rw [mem_parabolicHoms_iff]
    exact isParabolicHom_comp _ _ ((mem_parabolicHoms_iff).mp (hLpar x))
  have hwKT : ∀ (x : E1) (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r * p) ⊤ ℓ K (wK x) = algebraMap 𝒪 K (a ℓ) • wK x := by
    intro x ℓ _ hℓ hℓS hℓN
    simp only [hwK]
    rw [heckeT_castL, hLT x ℓ hℓ hℓS hℓN, cast_smul]
  have hwKU : ∀ x : E1, heckeT (N * r * p) ⊤ p K (wK x) = algebraMap 𝒪 K u • wK x := by
    intro x
    simp only [hwK]
    rw [heckeT_castL, hLU x, cast_smul]
  have hwKq : ∀ (x : E1) (q : ℕ) [NeZero q], q.Prime → q ∣ N →
      heckeT (N * r * p) ⊤ q K (wK x) = algebraMap 𝒪 K (cq q) • wK x := by
    intro x q _ hq hqN
    simp only [hwK]
    rw [heckeT_castL, hLq x q hq hqN, cast_smul]

  set ParK := parabolicHoms K (GammaH (N * r) ⊤) K with hParK
  set J : (ParK × ParK) →ₗ[K] H1 (N * r * p) ⊤ K :=
    (iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t) ∘ₗ ParK.subtype ∘ₗ LinearMap.fst K ParK ParK +
    (iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt) ∘ₗ ParK.subtype ∘ₗ LinearMap.snd K ParK ParK with hJ
  have hJapply : ∀ y : ParK × ParK, J y = iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t (y.1 : H1 (N * r) ⊤ K)
      + iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt (y.2 : H1 (N * r) ⊤ K) := fun y => rfl
  have hJinj : Function.Injective J := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y₁, y₂⟩ hy
    rw [hJapply] at hy
    obtain ⟨h₁0, h₂0⟩ := eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms (N * r) p hpNr h1t hpt
      (y₁ : H1 (N * r) ⊤ K) (y₂ : H1 (N * r) ⊤ K) y₁.2 y₂.2 hy
    ext <;> simp [h₁0, h₂0]
  set eJ := LinearEquiv.ofInjective J hJinj with heJ

  have hmemJ : ∀ x : E1, wK x ∈ LinearMap.range J := by
    intro x
    obtain ⟨y₁, y₂, hy₁, hy₂, -, heq⟩ :=
      exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul (N * r) p hpNr h1t hpt S
        (fun ℓ => algebraMap 𝒪 K (a ℓ)) (wK x) (hwKpar x)
        (fun ℓ _ hℓ hℓS hℓN => hwKT x ℓ hℓ hℓS hℓN)
        ⟨x₀, hx₀ne, hx₀par, fun ℓ _ hℓ hℓS hℓN => hx₀T ℓ hℓ hℓS hℓN⟩
    exact ⟨(⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩), heq.symm⟩

  set D : E1 → ParK × ParK := fun x => eJ.symm ⟨wK x, hmemJ x⟩ with hD
  have hDspec : ∀ x, J (D x) = wK x := fun x => by
    have h := LinearEquiv.ofInjective_apply J (h := hJinj) (eJ.symm ⟨wK x, hmemJ x⟩)
    simp only [heJ, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hwKadd : ∀ x y : E1, wK (x + y) = wK x + wK y := fun x y => by
    simp only [hwK, hLadd, map_add]
  have hwKsmul : ∀ (c : 𝒪) (x : E1), wK (c • x) = algebraMap 𝒪 K c • wK x := fun c x => by
    simp only [hwK, hLsmul, cast_smul]
  have hDadd : ∀ x y : E1, D (x + y) = D x + D y := fun x y =>
    hJinj (by rw [map_add, hDspec, hDspec, hDspec, hwKadd])
  have hDsmul : ∀ (c : 𝒪) (x : E1), D (c • x) = algebraMap 𝒪 K c • D x := fun c x =>
    hJinj (by rw [LinearMap.map_smul, hDspec, hDspec, hwKsmul])
  have hJT : ∀ (y : ParK × ParK) (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * r * p →
      heckeT (N * r * p) ⊤ ℓ K (J y) =
        iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t (heckeT (N * r) ⊤ ℓ K (y.1 : H1 (N * r) ⊤ K)) +
        iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt (heckeT (N * r) ⊤ ℓ K (y.2 : H1 (N * r) ⊤ K)) := by
    intro y ℓ _ hℓ hℓN
    have hℓp : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ Fact.out).mpr (by
      rintro rfl; exact hℓN (dvd_mul_left _ _))
    rw [hJapply, map_add, iDegL_eq_iDeg', iDegL_eq_iDeg', iDegL_eq_iDeg', iDegL_eq_iDeg',
      ← iDeg_heckeT_comm_of_coprime h1t (Nat.coprime_one_right ℓ) hℓ hℓN,
      ← iDeg_heckeT_comm_of_coprime hpt hℓp hℓ hℓN]
  have hJq : ∀ (y : ParK × ParK) (q : ℕ) [NeZero q], q.Prime → q ∣ N →
      heckeT (N * r * p) ⊤ q K (J y) =
        iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t (heckeT (N * r) ⊤ q K (y.1 : H1 (N * r) ⊤ K)) +
        iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt (heckeT (N * r) ⊤ q K (y.2 : H1 (N * r) ⊤ K)) := by
    intro y q _ hq hqN
    have hqp : Nat.Coprime q p := (Nat.coprime_primes hq Fact.out).mpr
      (fun h => hpNr (h ▸ hqN.mul_right r))
    rw [hJapply, map_add, iDegL_eq_iDeg', iDegL_eq_iDeg', iDegL_eq_iDeg', iDegL_eq_iDeg',
      ← iDeg_heckeT_comm_of_dvd h1t (Nat.coprime_one_right q) (hqN.mul_right r),
      ← iDeg_heckeT_comm_of_dvd hpt hqp (hqN.mul_right r)]

  have hJU : ∀ (y : ParK × ParK), heckeT (N * r * p) ⊤ p K (J y) =
      iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t
          (heckeT (N * r) ⊤ p K (y.1 : H1 (N * r) ⊤ K) + (p : K) • (y.2 : H1 (N * r) ⊤ K))
        - iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt (y.1 : H1 (N * r) ⊤ K) := by
    intro y
    have e1 := heckeT_iDeg_interchange (A := K) Fact.out hpNr h1t hpt (y.1 : H1 (N * r) ⊤ K)
    have e2 := heckeT_iDeg_q_eq_smul (A := K) h1t hpt (y.2 : H1 (N * r) ⊤ K)
    rw [hJapply, map_add, map_add, LinearMap.map_smul, Nat.cast_smul_eq_nsmul]
    simp only [iDegL_eq_iDeg'] at e1 e2 ⊢
    rw [e1, e2]
    abel

  have hParT : ∀ (ℓ : ℕ) [NeZero ℓ] (y : H1 (N * r) ⊤ K), y ∈ ParK → heckeT (N * r) ⊤ ℓ K y ∈ ParK :=
    fun ℓ _ y hy => by
      simp only [hParK] at hy ⊢
      rw [mem_parabolicHoms_iff_int] at hy ⊢
      exact heckeT_mem_parabolicHoms (N * r) ⊤ K ℓ y hy

  have huniq : ∀ (y₁ y₂ z₁ z₂ : H1 (N * r) ⊤ K), y₁ ∈ ParK → y₂ ∈ ParK → z₁ ∈ ParK → z₂ ∈ ParK →
      iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t y₁ + iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt y₂ =
        iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t z₁ + iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt z₂ →
      y₁ = z₁ ∧ y₂ = z₂ := by
    intro y₁ y₂ z₁ z₂ hy₁ hy₂ hz₁ hz₂ h
    have h' : iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t (y₁ - z₁) +
        iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt (y₂ - z₂) = 0 := by
      rw [map_sub, map_sub, ← sub_eq_zero.mpr h]; abel
    obtain ⟨e1, e2⟩ := eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms (N * r) p hpNr h1t hpt
      (y₁ - z₁) (y₂ - z₂) (sub_mem hy₁ hz₁) (sub_mem hy₂ hz₂) h'
    exact ⟨sub_eq_zero.mp e1, sub_eq_zero.mp e2⟩

  set Y₁ : E1 → H1 (N * r) ⊤ K := fun x => ((D x).1 : H1 (N * r) ⊤ K) with hY₁
  set Y₂ : E1 → H1 (N * r) ⊤ K := fun x => ((D x).2 : H1 (N * r) ⊤ K) with hY₂
  have hY₁par : ∀ x, Y₁ x ∈ ParK := fun x => (D x).1.2
  have hY₂par : ∀ x, Y₂ x ∈ ParK := fun x => (D x).2.2
  have hYdec : ∀ x, wK x = iDegL (N * r) (N * r * p) ⊤ ⊤ 1 K K h1t (Y₁ x) +
      iDegL (N * r) (N * r * p) ⊤ ⊤ p K K hpt (Y₂ x) := fun x => by
    rw [← hDspec, hJapply]
  have hY₁add : ∀ x y, Y₁ (x + y) = Y₁ x + Y₁ y := fun x y => by
    simp only [hY₁, hDadd, Prod.fst_add, Submodule.coe_add]
  have hY₁smul : ∀ (c : 𝒪) (x : E1), Y₁ (c • x) = algebraMap 𝒪 K c • Y₁ x := fun c x => by
    simp only [hY₁, hDsmul, Prod.smul_fst, Submodule.coe_smul]

  have hY_T : ∀ (x : E1) (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r) ⊤ ℓ K (Y₁ x) = algebraMap 𝒪 K (a ℓ) • Y₁ x ∧
      heckeT (N * r) ⊤ ℓ K (Y₂ x) = algebraMap 𝒪 K (a ℓ) • Y₂ x := by
    intro x ℓ _ hℓ hℓS hℓN
    apply huniq _ _ _ _ (hParT ℓ _ (hY₁par x)) (hParT ℓ _ (hY₂par x))
      (Submodule.smul_mem _ _ (hY₁par x)) (Submodule.smul_mem _ _ (hY₂par x))
    have e := hJT (D x) ℓ hℓ hℓN
    rw [hDspec, hwKT x ℓ hℓ hℓS hℓN, hYdec, smul_add, ← LinearMap.map_smul, ← LinearMap.map_smul] at e
    exact e.symm

  have hY_q : ∀ (x : E1) (q : ℕ) [NeZero q], q.Prime → q ∣ N →
      heckeT (N * r) ⊤ q K (Y₁ x) = algebraMap 𝒪 K (cq q) • Y₁ x := by
    intro x q _ hq hqN
    refine (huniq _ _ (algebraMap 𝒪 K (cq q) • Y₁ x) (algebraMap 𝒪 K (cq q) • Y₂ x)
      (hParT q _ (hY₁par x)) (hParT q _ (hY₂par x))
      (Submodule.smul_mem _ _ (hY₁par x)) (Submodule.smul_mem _ _ (hY₂par x)) ?_).1
    have e := hJq (D x) q hq hqN
    rw [hDspec, hwKq x q hq hqN, hYdec, smul_add, ← LinearMap.map_smul, ← LinearMap.map_smul] at e
    exact e.symm

  have hY_U : ∀ x : E1,
      heckeT (N * r) ⊤ p K (Y₁ x) + (p : K) • Y₂ x = algebraMap 𝒪 K u • Y₁ x ∧
      -(Y₁ x) = algebraMap 𝒪 K u • Y₂ x := by
    intro x
    apply huniq _ _ _ _ (add_mem (hParT p _ (hY₁par x)) (Submodule.smul_mem _ _ (hY₂par x)))
      (neg_mem (hY₁par x)) (Submodule.smul_mem _ _ (hY₁par x)) (Submodule.smul_mem _ _ (hY₂par x))
    have e := hJU (D x)
    rw [hDspec, hwKU x, hYdec, smul_add, ← LinearMap.map_smul, ← LinearMap.map_smul] at e
    rw [map_neg, ← sub_eq_add_neg]
    exact e.symm
  have hu' : algebraMap 𝒪 K u ≠ 0 := fun h => hu (hinjOK (by rw [h, map_zero]))

  let Φ : E1 →ₗ[𝒪] H1 (N * r) H₀ K :=
    { toFun := fun x => iDegL (N * r) (N * r) ⊤ H₀ 1 K K h₀ (Y₁ x)
      map_add' := fun x y => by rw [hY₁add, map_add]
      map_smul' := fun c x => by rw [hY₁smul, LinearMap.map_smul, RingHom.id_apply, algebraMap_smul] }
  have hΦapply : ∀ x, Φ x = iDegL (N * r) (N * r) ⊤ H₀ 1 K K h₀ (Y₁ x) := fun x => rfl
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    rw [hΦapply] at hx
    have h1 : Y₁ x = 0 := hres₀inj (by rw [hx, map_zero])
    have h2 : Y₂ x = 0 := by
      have := (hY_U x).2
      rw [h1, neg_zero] at this
      exact (smul_eq_zero.mp this.symm).resolve_left hu'
    have h3 : wK x = 0 := by rw [hYdec, h1, h2, map_zero, map_zero, add_zero]
    have h4 : L x = 0 := hcK1tinj (by simpa [hwK] using h3)
    have h5 : (x : H1 (N * r * p) H 𝒪) = 0 := by rw [← hLeq x, h4, map_zero]
    exact_mod_cast h5

  have hΦdia : ∀ (x : E1) (σ : Gamma0 (N * r)), diamondRaw (N * r) H₀ K σ (Φ x) = Φ x := by
    intro x σ
    have : Φ x ∈ Set.range (iDeg' (N * r) (N * r) ⊤ H₀ 1 K h₀) := ⟨Y₁ x, rfl⟩
    rw [hres₀range] at this
    exact this σ
  have hΦT : ∀ (x : E1) (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r →
      heckeT (N * r) H₀ ℓ K (Φ x) = algebraMap 𝒪 K (a ℓ) • Φ x := by
    intro x ℓ _ hℓ hℓS hℓNr
    have hℓp : ℓ ≠ p := by rintro rfl; exact hℓS hpS
    have hℓN : ¬ ℓ ∣ N * r * p := by
      intro h
      rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
      · exact hℓNr h
      · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h)
    rw [hΦapply, iDegL_eq_iDeg', ← iDeg_heckeT_comm_of_coprime h₀ (Nat.coprime_one_right ℓ) hℓ hℓNr,
      (hY_T x ℓ hℓ hℓS hℓN).1, ← iDegL_eq_iDeg' (R := K), LinearMap.map_smul]
    rfl
  have hΦq : ∀ (x : E1) (q : ℕ) [NeZero q], q.Prime → q ∣ N →
      heckeT (N * r) H₀ q K (Φ x) = algebraMap 𝒪 K (cq q) • Φ x := by
    intro x q _ hq hqN
    rw [hΦapply, iDegL_eq_iDeg', ← iDeg_heckeT_comm_of_dvd h₀ (Nat.coprime_one_right q) (hqN.mul_right r),
      hY_q x q hq hqN, ← iDegL_eq_iDeg' (R := K), LinearMap.map_smul]
    rfl

  have hΦint : ∀ x : E1, ∃ c : 𝒪, c ≠ 0 ∧ ∃ m ∈ E0, castL 𝒪 K (N * r) H₀ m = algebraMap 𝒪 K c • Φ x := by
    intro x

    obtain ⟨n, b, hb⟩ := exists_basis_parabolicHoms_of_isAddTorsionFree (GammaH (N * r) ⊤)
    obtain ⟨bK, hbK⟩ := hb K
    obtain ⟨b𝒪, hb𝒪⟩ := hb 𝒪
    have hcast_b : ∀ i, castL 𝒪 K (N * r) ⊤ (b𝒪 i : H1 (N * r) ⊤ 𝒪) = (bK i : H1 (N * r) ⊤ K) := by
      intro i
      rw [castL_apply]
      erw [hb𝒪 i, hbK i]
      ext g
      simp

    set coord : Fin n → K := fun i => bK.repr ⟨Y₁ x, hY₁par x⟩ i with hcoord
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors 𝒪)
      (Finset.univ.image coord)
    have hc' : ∀ i, IsLocalization.IsInteger 𝒪 ((c : 𝒪) • coord i) := fun i =>
      hc (coord i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    choose d hd using hc'
    refine ⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩
    set m₁ : H1 (N * r) ⊤ 𝒪 := ∑ i, d i • (b𝒪 i : H1 (N * r) ⊤ 𝒪) with hm₁
    have hm₁K : castL 𝒪 K (N * r) ⊤ m₁ = algebraMap 𝒪 K c • Y₁ x := by
      have hrepr : (⟨Y₁ x, hY₁par x⟩ : ParK) = ∑ i, coord i • bK i := by
        rw [← bK.sum_repr ⟨Y₁ x, hY₁par x⟩]
      have hrepr' : Y₁ x = ∑ i, coord i • (bK i : H1 (N * r) ⊤ K) := by
        have := congrArg (fun z : ParK => (z : H1 (N * r) ⊤ K)) hrepr
        simpa [Submodule.coe_sum, Submodule.coe_smul] using this
      rw [hm₁, map_sum, hrepr', Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [cast_smul, hcast_b, hd i, smul_assoc, algebraMap_smul]
    refine ⟨iDegL (N * r) (N * r) ⊤ H₀ 1 𝒪 𝒪 h₀ m₁, ?_, ?_⟩
    ·
      have hmK : castL 𝒪 K (N * r) H₀ (iDegL (N * r) (N * r) ⊤ H₀ 1 𝒪 𝒪 h₀ m₁) =
          algebraMap 𝒪 K c • Φ x := by
        rw [← iDegL_castL, hm₁K, LinearMap.map_smul, hΦapply]
      apply hE0mem
      · intro σ
        apply hcK0inj
        rw [← diamondRaw_castL, hmK, diamondRaw_smul', hΦdia]
      · intro ℓ _ hℓ hℓS hℓNr
        apply hcK0inj
        rw [← heckeT_castL, hmK, heckeT_smul', hΦT x ℓ hℓ hℓS hℓNr, cast_smul, hmK, smul_comm]
      · intro q _ hq hqN
        apply hcK0inj
        rw [← heckeT_castL, hmK, heckeT_smul', hΦq x q hq hqN, cast_smul, hmK, smul_comm]
    · rw [← iDegL_castL, hm₁K, LinearMap.map_smul, hΦapply]

  exact Module.finrank_le_of_forall_exists_smul_eq_of_isFractionRing (K := K) Φ hΦinj E0
    (castL 𝒪 K (N * r) H₀) hΦint

end Core
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.CohCarrier"

end Rg6
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.CohCarrier"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "Polynomial IsLocalRing CohCarrier P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.CohCarrier IharaLemma IharaTower"

namespace Rg6

section Corner

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
  (Sp : IdempotentSplitting B) (i : Fin Sp.n)

theorem coe_toCornerRing_smul (b : B) (x : ↥(cornerSubmodule (M := V) (Sp.e i))) :
    ((Sp.toCornerRing i b • x : ↥(cornerSubmodule (M := V) (Sp.e i))) : V) = b • (x : V) := by
  rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_toCornerRing,
    show Sp.e i * b * Sp.e i = b * Sp.e i by rw [mul_comm (Sp.e i) b, mul_assoc, (Sp.idem i).eq],
    mul_smul, Sp.e_smul_coe i x]

theorem smul_coe_eq_of_mem_torsionBySet (χ : Sp.CornerRing i →ₐ[𝒪] 𝒪)
    (x : ↥(cornerSubmodule (M := V) (Sp.e i)))
    (hx : x ∈ Submodule.torsionBySet (Sp.CornerRing i) ↥(cornerSubmodule (M := V) (Sp.e i))
      ↑(RingHom.ker χ))
    (b : B) : b • (x : V) = χ (Sp.toCornerRing i b) • (x : V) := by
  have hmem : Sp.toCornerRing i b - algebraMap 𝒪 (Sp.CornerRing i) (χ (Sp.toCornerRing i b)) ∈
      RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have h0 := Submodule.mem_torsionBySet_iff _ _ |>.mp hx ⟨_, hmem⟩
  rw [Subtype.coe_mk, sub_smul, sub_eq_zero, algebraMap_smul] at h0
  rw [← coe_toCornerRing_smul, h0, Submodule.coe_smul_of_tower]

theorem cornerSmul_eq_of_mem_torsionBySet (χ : Sp.CornerRing i →ₐ[𝒪] 𝒪)
    (x : ↥(cornerSubmodule (M := V) (Sp.e i)))
    (hx : x ∈ Submodule.torsionBySet (Sp.CornerRing i) ↥(cornerSubmodule (M := V) (Sp.e i))
      ↑(RingHom.ker χ))
    (z : Sp.CornerRing i) : z • x = χ z • x := by
  have hmem : z - algebraMap 𝒪 (Sp.CornerRing i) (χ z) ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have h0 := Submodule.mem_torsionBySet_iff _ _ |>.mp hx ⟨_, hmem⟩
  rwa [Subtype.coe_mk, sub_smul, sub_eq_zero, algebraMap_smul] at h0

theorem sub_mem_maximalIdeal_of_smul_eq [IsLocalRing 𝒪] (t : B) (c lam : 𝒪)
    (ht : t - algebraMap 𝒪 B c ∈ Sp.𝔪 i) (v : V)
    (hv : v ∈ cornerSubmodule (M := V) (Sp.e i)) (hv0 : v ≠ 0) (hact : t • v = lam • v) :
    lam - c ∈ maximalIdeal 𝒪 := by
  by_contra hunit
  have hu : IsUnit (lam - c) := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hunit

  set z : Sp.CornerRing i := algebraMap B (Sp.CornerRing i) (t - algebraMap 𝒪 B c) with hz
  have hzmax : z ∈ maximalIdeal (Sp.CornerRing i) := by
    rw [hz, IsLocalization.AtPrime.to_map_mem_maximal_iff (Sp.CornerRing i) (Sp.𝔪 i)]
    exact ht
  have hw : IsUnit (algebraMap 𝒪 (Sp.CornerRing i) (lam - c) - z) := by
    by_contra hnu
    have hmem : algebraMap 𝒪 (Sp.CornerRing i) (lam - c) - z ∈ maximalIdeal (Sp.CornerRing i) := by
      simpa [mem_maximalIdeal, mem_nonunits_iff] using hnu
    have : algebraMap 𝒪 (Sp.CornerRing i) (lam - c) ∈ maximalIdeal (Sp.CornerRing i) := by
      have := add_mem hmem hzmax
      simpa using this
    exact (mem_maximalIdeal _).mp this ((hu.map _))

  set x : ↥(cornerSubmodule (M := V) (Sp.e i)) := ⟨v, hv⟩ with hx
  have hzx : z • x = (lam - c) • x := by
    apply Subtype.ext
    have e1 : z = Sp.toCornerRing i (t - algebraMap 𝒪 B c) := Subtype.ext rfl
    rw [e1, coe_toCornerRing_smul, Submodule.coe_smul_of_tower]
    show (t - algebraMap 𝒪 B c) • v = (lam - c) • v
    rw [sub_smul, hact, algebraMap_smul, sub_smul]
  have hzero : x = 0 := by
    have h1 : (algebraMap 𝒪 (Sp.CornerRing i) (lam - c) - z) • x = 0 := by
      rw [sub_smul, algebraMap_smul, hzx, sub_self]
    exact (hw.smul_left_cancel).mp (by rw [h1, smul_zero])
  exact hv0 (congrArg Subtype.val hzero)

end Corner
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.CohCarrier"

end Rg6
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.CohCarrier"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (hord : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (N : ℕ) [NeZero N] [NeZero (N * p)] (hpN : ¬ p ∣ N) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)

    (Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hNunr : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ N → q ^ 2 ∣ N)
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) (hrS : r ∉ S) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)

    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)
    [Fact (CuspForm.HasIntegralStructure (N * p) 2)]
    (θ₁ : CuspForm.heckeAlgebra (N * p) 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N * p) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (πT₀ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] 𝒪)
    (πT₁ : CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁ →ₐ[𝒪] 𝒪)
    (hπ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓ₁ : ¬ ℓ ∣ N * p) (hℓ₀ : ¬ ℓ ∣ N),
      πT₁ (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓ₁ hℓS)) =
        πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓ₀ hℓS)))
    (H₀ : Subgroup (ZMod (N * r))ˣ) [NeZero (N * r)]
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1)

    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 (N * r) H₀ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 (N * r) H₀ 𝒪)]
    (S₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin S₀.n)
    (e₀ : S₀.CornerRing i₀ ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))]
    (tp : S₀.CornerRing i₀)
    (hT₀ : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r)
        (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))),
      ((e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
          : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ ℓ 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (htp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsUnit tp ∧ (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪)) ∧
      (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeTlower (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪)))
    (hocc₀ : Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) ↑(RingHom.ker (πT₀.comp e₀.toAlgHom)) ≠ ⊥)
    (hrk₀ : Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) =
      Module.finrank 𝒪 (Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
        ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))) * Module.finrank 𝒪 (S₀.CornerRing i₀))
    (hgen : ∀ t : 𝕋₀, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily (N * r) H₀ (↑S : Set ℕ) 𝒪)),
      ∀ m : H1 (N * r) H₀ 𝒪, t • m = f m)
    (tfull : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝕋₀)
    (htfull : ∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      ∀ m : H1 (N * r) H₀ 𝒪, tfull g • m = CohCarrier.opFamily (N * r) H₀ (↑S : Set ℕ) 𝒪 g m)
    (cfull : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝒪)
    (hcfull : ∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      tfull g - algebraMap 𝒪 𝕋₀ (cfull g) ∈ S₀.𝔪 i₀)
    (hcofull : ∀ v : H1 (N * r) H₀ 𝒪, (∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋₀ (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r) H₀ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
    (hfaith₀ : ∀ t : S₀.CornerRing i₀, (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), t • m = 0) → t = 0)

    (hdia : ∀ (σ : ↥(CongruenceSubgroup.Gamma0 (N * r))) (v : H1 (N * r) H₀ 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) → diamondRaw (N * r) H₀ 𝒪 σ v = v)

    (αt : S₀.CornerRing i₀)
    (hαt : IsUnit αt ∧ αt * αt - tp * αt + algebraMap 𝒪 (S₀.CornerRing i₀) (p : 𝒪) = 0 ∧
      αt - tp ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 (S₀.CornerRing i₀)))

    [NeZero (N * r * p)] (H : Subgroup (ZMod (N * r * p))ˣ)
      (hH : H = H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)))
      {𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
      [Module 𝕋ₐ (H1 (N * r * p) H 𝒪)] [Module 𝕋₁ (H1 (N * r * p) H 𝒪)]
      [IsScalarTower 𝒪 𝕋ₐ (H1 (N * r * p) H 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * r * p) H 𝒪)]
      [Module.Finite 𝒪 𝕋ₐ] [Module.Finite 𝒪 𝕋₁]
      (ι : 𝕋ₐ →ₐ[𝒪] 𝕋₁) (hι : ∀ (t : 𝕋ₐ) (v : H1 (N * r * p) H 𝒪), ι t • v = t • v)
      (U : 𝕋₁) (hU : ∀ v : H1 (N * r * p) H 𝒪, U • v = heckeT (N * r * p) H p 𝒪 v)
      (hgen₁ : Algebra.adjoin 𝒪 (Set.range ι ∪ {U}) = ⊤)
      (Sₐ : IdempotentSplitting 𝕋ₐ) (iₐ : Fin Sₐ.n) (S₁ : IdempotentSplitting 𝕋₁) (i₁ : Fin S₁.n)
      (e₁ : S₁.CornerRing i₁ ≃ₐ[𝒪] CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁)
      [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))]
      [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))]
      [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))]
      [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))]

      (h₁ₐ : LevelLE (N * r * p) (N * r * p) ⊤ H 1)
    (tA : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝕋ₐ) (dA : (ZMod (N * r * p))ˣ → 𝕋ₐ)
    (hE :

      (∀ g : CohCarrier.Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) →
        ∀ v : H1 (N * r * p) H 𝒪, tA g • v = (match g with
            | .T ℓ hℓ _ _ => (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT (N * r * p) H ℓ 𝒪 v)
            | .U q hq _ => (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT (N * r * p) H q 𝒪 v)
            | .dia _ => v)) ∧
      (∀ g : CohCarrier.Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) →
        tA g - algebraMap 𝒪 𝕋ₐ (cfull g) ∈ Sₐ.𝔪 iₐ) ∧
      (∀ (d : (ZMod (N * r * p))ˣ) (v : H1 (N * r * p) H 𝒪), dA d • v = diamondL (N * r * p) H 𝒪 d v) ∧
      (∀ d : (ZMod (N * r * p))ˣ, dA d - 1 ∈ Sₐ.𝔪 iₐ) ∧
      Algebra.adjoin 𝒪 (tA '' {g | (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False)} ∪ Set.range dA) = ⊤ ∧

      (∀ v : H1 (N * r * p) H 𝒪, v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ) →
        v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * r * p) ⊤) 𝒪).map
          (iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ)) ∧

      (S₁.𝔪 i₁).comap ι = Sₐ.𝔪 iₐ ∧ U ∉ S₁.𝔪 i₁ ∧

      (∀ a : 𝒪, αt - algebraMap 𝒪 (S₀.CornerRing i₀) a ∈ IsLocalRing.maximalIdeal (S₀.CornerRing i₀) →
        U - algebraMap 𝒪 𝕋₁ a ∈ S₁.𝔪 i₁) ∧
      (∀ v : H1 (N * r * p) H 𝒪, v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁) →
        v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))  ∧

      (∃ φ : (Sₐ.CornerRing iₐ) →ₐ[𝒪] (S₁.CornerRing i₁), Function.Surjective φ ∧
        (∀ (t : (Sₐ.CornerRing iₐ)) (x : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))) (x₁ : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))),
          (x : H1 (N * r * p) H 𝒪) = x₁ → ((t • x : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))) : H1 (N * r * p) H 𝒪) = (φ t • x₁ : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)))) ∧
        (∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N * p) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r * p)
            (m : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))),
          ((e₁.symm (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
              : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))) : H1 (N * r * p) H 𝒪) = heckeT (N * r * p) H ℓ 𝒪 (m : H1 (N * r * p) H 𝒪))) ∧

      (∀ t : S₁.CornerRing i₁, (∀ m' : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)), t • m' = 0) → t = 0) ∧
      Submodule.torsionBySet (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)) ↑(RingHom.ker (πT₁.comp e₁.toAlgHom)) ≠ ⊥ ∧
      Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)) =
        Module.finrank 𝒪 (Submodule.torsionBySet (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))
          ↑(RingHom.ker (πT₁.comp e₁.toAlgHom))) * Module.finrank 𝒪 (S₁.CornerRing i₁)  ∧

      (∀ (a : 𝒪) (m' : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))), a ≠ 0 →
        a • m' ∈ (RingHom.ker (πT₁.comp e₁.toAlgHom) • ⊤ : Submodule (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))).restrictScalars 𝒪 →
        m' ∈ (RingHom.ker (πT₁.comp e₁.toAlgHom) • ⊤ : Submodule (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))).restrictScalars 𝒪))

    (h1 : LevelLE (N * r) (N * r * p) H₀ H 1) (hp' : LevelLE (N * r) (N * r * p) H₀ H p)
    (hLa : ∀ (k : Fin 2) (v : H1 (N * r) H₀ 𝒪), v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) →
      ![iDegL (N * r) (N * r * p) H₀ H 1 𝒪 𝒪 h1, iDegL (N * r) (N * r * p) H₀ H p 𝒪 𝒪 hp'] k v
        ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))
    (hLc : ∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      iDegL (N * r) (N * r * p) H₀ H 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪)
          - iDegL (N * r) (N * r * p) H₀ H p 𝒪 𝒪 hp' (m : H1 (N * r) H₀ 𝒪)
        ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)) :
    Module.finrank 𝒪 ((Submodule.torsionBySet (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))
        ↑(RingHom.ker (πT₁.comp e₁.toAlgHom))).restrictScalars 𝒪) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
        ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))).restrictScalars 𝒪) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpp : p.Prime := Fact.out
  obtain ⟨hEtA, hEcf, hEdA, hEdA1, hEadj, hE4, hEcomap, hEUnot, hEord, hEsub,
    ⟨φ₁, hφsurj, hφact, hET⟩, hEfaith, hEocc, hErk, hEsat⟩ := hE

  have hpr : p ≠ r := by
    rintro rfl; exact hrN (dvd_mul_left p N)
  have hpNr : ¬ p ∣ N * r := by
    intro h
    rcases hpp.dvd_mul.mp h with h | h
    · exact hpN h
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hpp hr).mp h)
  have hNr0 : 0 < N * r := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1t : LevelLE (N * r) (N * r * p) ⊤ ⊤ 1 :=
    ⟨dvd_mul_right _ _, one_dvd _, fun _ _ => Subgroup.mem_top _⟩
  have hpt : LevelLE (N * r) (N * r * p) ⊤ ⊤ p :=
    ⟨dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left p hNr0], fun _ _ => Subgroup.mem_top _⟩
  have h₀ : LevelLE (N * r) (N * r) ⊤ H₀ 1 :=
    ⟨dvd_rfl, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

  set χ₁ : S₁.CornerRing i₁ →ₐ[𝒪] 𝒪 := πT₁.comp e₁.toAlgHom with hχ₁
  set χ₀ : S₀.CornerRing i₀ →ₐ[𝒪] 𝒪 := πT₀.comp e₀.toAlgHom with hχ₀
  set ψ₁ : 𝕋₁ →+* 𝒪 := (χ₁ : S₁.CornerRing i₁ →+* 𝒪).comp (S₁.toCornerRing i₁) with hψ₁
  have hψ₁ap : ∀ t : 𝕋₁, ψ₁ t = χ₁ (S₁.toCornerRing i₁ t) := fun t => rfl
  let a : ℕ → 𝒪 := fun ℓ => if h : ℓ.Prime ∧ ℓ ∉ (↑S : Set ℕ) ∧ ¬ ℓ ∣ N then
      πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T h.1 h.2.2 h.2.1)) else 0
  have ha : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
      a ℓ = πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := by
    intro ℓ hℓ hℓS hℓN
    simp only [a, dif_pos (show ℓ.Prime ∧ ℓ ∉ (↑S : Set ℕ) ∧ ¬ ℓ ∣ N from ⟨hℓ, hℓS, hℓN⟩)]
  let u : 𝒪 := ψ₁ U
  let cq : ℕ → 𝒪 := fun q => if h : q.Prime ∧ q ∣ N then
      ψ₁ (ι (tA (CohCarrier.Gen.U q h.1 (h.2.mul_right r)))) else 0
  have hcq : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
      cq q = ψ₁ (ι (tA (CohCarrier.Gen.U q hq (hqN.mul_right r)))) := by
    intro q hq hqN
    simp only [cq, dif_pos (show q.Prime ∧ q ∣ N from ⟨hq, hqN⟩)]

  set M₁ := cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁) with hM₁
  set M₀ := cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) with hM₀
  set T₁ := Submodule.torsionBySet (S₁.CornerRing i₁) ↥M₁ ↑(RingHom.ker χ₁) with hT₁def
  set T₀ := Submodule.torsionBySet (S₀.CornerRing i₀) ↥M₀ ↑(RingHom.ker χ₀) with hT₀def
  let f₁ : ↥(T₁.restrictScalars 𝒪) →ₗ[𝒪] H1 (N * r * p) H 𝒪 :=
    { toFun := fun x => ((x : ↥M₁) : H1 (N * r * p) H 𝒪)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let f₀ : ↥(T₀.restrictScalars 𝒪) →ₗ[𝒪] H1 (N * r) H₀ 𝒪 :=
    { toFun := fun x => ((x : ↥M₀) : H1 (N * r) H₀ 𝒪)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf₁inj : Function.Injective f₁ := fun x y h => Subtype.ext (Subtype.ext h)
  have hf₀inj : Function.Injective f₀ := fun x y h => Subtype.ext (Subtype.ext h)
  set E1 : Submodule 𝒪 (H1 (N * r * p) H 𝒪) := LinearMap.range f₁ with hE1
  set E0 : Submodule 𝒪 (H1 (N * r) H₀ 𝒪) := LinearMap.range f₀ with hE0
  have hfin1 : Module.finrank 𝒪 E1 = Module.finrank 𝒪 ↥(T₁.restrictScalars 𝒪) :=
    LinearMap.finrank_range_of_inj hf₁inj
  have hfin0 : Module.finrank 𝒪 E0 = Module.finrank 𝒪 ↥(T₀.restrictScalars 𝒪) :=
    LinearMap.finrank_range_of_inj hf₀inj

  have hmemE1 : ∀ v ∈ E1, ∃ x : ↥M₁, x ∈ T₁ ∧ (x : H1 (N * r * p) H 𝒪) = v := by
    rintro v ⟨x, rfl⟩; exact ⟨(x : ↥M₁), x.2, rfl⟩
  have hmemE0 : ∀ m ∈ E0, ∃ x : ↥M₀, x ∈ T₀ ∧ (x : H1 (N * r) H₀ 𝒪) = m := by
    rintro m ⟨x, rfl⟩; exact ⟨(x : ↥M₀), x.2, rfl⟩
  have hmkE0 : ∀ (x : ↥M₀), x ∈ T₀ → (x : H1 (N * r) H₀ 𝒪) ∈ E0 := fun x hx => ⟨⟨x, hx⟩, rfl⟩

  have hM₁subₐ : ∀ v : H1 (N * r * p) H 𝒪, v ∈ M₁ →
      v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ) := hEsub
  have hE1par : ∀ v ∈ E1, v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * r * p) ⊤) 𝒪).map
      (iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ) := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := hmemE1 v hv
    exact hE4 _ (hM₁subₐ _ x.2)

  have hψact : ∀ (x : ↥M₁), x ∈ T₁ → ∀ t : 𝕋₁, t • (x : H1 (N * r * p) H 𝒪) = ψ₁ t • (x : H1 (N * r * p) H 𝒪) :=
    fun x hx t => Rg6.smul_coe_eq_of_mem_torsionBySet S₁ i₁ χ₁ x hx t
  have hE1T : ∀ v ∈ E1, ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r * p) H ℓ 𝒪 v = a ℓ • v := by
    intro v hv ℓ _ hℓ hℓS hℓNrp
    obtain ⟨x, hx, rfl⟩ := hmemE1 v hv
    have hℓS' : ℓ ∉ (↑S : Set ℕ) := by exact_mod_cast hℓS
    have hℓN : ¬ ℓ ∣ N := fun h => hℓNrp ((h.mul_right r).mul_right p)
    have hℓNp : ¬ ℓ ∣ N * p := by
      intro h
      rcases hℓ.dvd_mul.mp h with h | h
      · exact hℓN h
      · exact hℓNrp (h.trans (dvd_mul_left p _))
    have h1 := hET ℓ hℓ hℓNp hℓS' hℓNrp x
    rw [Rg6.cornerSmul_eq_of_mem_torsionBySet S₁ i₁ χ₁ x hx, Submodule.coe_smul_of_tower] at h1
    rw [← h1, ha ℓ hℓ hℓS' hℓN]
    congr 1
    simp only [hχ₁, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      AlgEquiv.apply_symm_apply]
    exact hπ ℓ hℓ hℓS' hℓNp hℓN
  have hE1U : ∀ v ∈ E1, heckeT (N * r * p) H p 𝒪 v = u • v := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hmemE1 v hv
    rw [← hU, hψact x hx U]
  have hE1q : ∀ v ∈ E1, ∀ (q : ℕ) [NeZero q], q.Prime → q ∣ N →
      heckeT (N * r * p) H q 𝒪 v = cq q • v := by
    intro v hv q _ hq hqN
    obtain ⟨x, hx, rfl⟩ := hmemE1 v hv
    have h1 := hEtA (CohCarrier.Gen.U q hq (hqN.mul_right r)) hqN (x : H1 (N * r * p) H 𝒪)
    rw [← hι, hψact x hx] at h1
    rw [hcq q hq hqN, h1]

  have hu : u ≠ 0 := by
    intro hu0
    apply hEUnot
    have hker : S₁.toCornerRing i₁ U ∈ RingHom.ker χ₁ := by
      rw [RingHom.mem_ker]; exact hu0
    have hle : RingHom.ker (χ₁ : S₁.CornerRing i₁ →+* 𝒪) ≤ maximalIdeal (S₁.CornerRing i₁) :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have hmax := hle hker
    have e1 : S₁.toCornerRing i₁ U = algebraMap 𝕋₁ (S₁.CornerRing i₁) U := Subtype.ext rfl
    rw [e1, IsLocalization.AtPrime.to_map_mem_maximal_iff (S₁.CornerRing i₁) (S₁.𝔪 i₁)] at hmax
    exact hmax

  have hE0ne : E0 ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hocc₀
    rw [Submodule.ne_bot_iff]
    refine ⟨(x : H1 (N * r) H₀ 𝒪), hmkE0 x hx, fun h => hx0 (Subtype.ext h)⟩
  have hE0T : ∀ m ∈ E0, ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r * p →
      heckeT (N * r) H₀ ℓ 𝒪 m = a ℓ • m := by
    intro m hm ℓ _ hℓ hℓS hℓNrp
    obtain ⟨x, hx, rfl⟩ := hmemE0 m hm
    have hℓS' : ℓ ∉ (↑S : Set ℕ) := by exact_mod_cast hℓS
    have hℓN : ¬ ℓ ∣ N := fun h => hℓNrp ((h.mul_right r).mul_right p)
    have hℓNr : ¬ ℓ ∣ N * r := fun h => hℓNrp (h.mul_right p)
    have h1 := hT₀ ℓ hℓ hℓN hℓS' hℓNr x
    rw [Rg6.cornerSmul_eq_of_mem_torsionBySet S₀ i₀ χ₀ x hx, Submodule.coe_smul_of_tower] at h1
    rw [← h1, ha ℓ hℓ hℓS' hℓN]
    congr 1
    simp only [hχ₀, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      AlgEquiv.apply_symm_apply]
  have hE0dia : ∀ m ∈ E0, ∀ σ : CongruenceSubgroup.Gamma0 (N * r), diamondRaw (N * r) H₀ 𝒪 σ m = m := by
    intro m hm σ
    obtain ⟨x, -, rfl⟩ := hmemE0 m hm
    exact hdia σ _ x.2

  have hSprod : 0 < N * r * p * ∏ s ∈ S, s := by
    refine Nat.pos_of_ne_zero (mul_ne_zero (NeZero.ne _) ?_)
    exact Finset.prod_ne_zero_iff.mpr fun s hs => (hS s hs).ne_zero
  obtain ⟨ℓ₁, A₁, σ₁, hℓ₁, hℓ₁M, hℓ₁mod, hA₁, hσ₁, heval⟩ :=
    ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
      ρbar habs (N * r) hSprod
  haveI : NeZero ℓ₁ := ⟨hℓ₁.ne_zero⟩
  have hℓ₁Nrp : ¬ ℓ₁ ∣ N * r * p := fun h => hℓ₁M (h.mul_right _)
  have hℓ₁N : ¬ ℓ₁ ∣ N := fun h => hℓ₁Nrp ((h.mul_right r).mul_right p)
  have hℓ₁S : ℓ₁ ∉ S := fun h => hℓ₁M ((Finset.dvd_prod_of_mem _ h).mul_left _)
  have hℓ₁S' : ℓ₁ ∉ (↑S : Set ℕ) := by exact_mod_cast hℓ₁S
  have hℓ₁unit : IsUnit (a ℓ₁ - ((ℓ₁ : 𝒪) + 1)) := by

    have hres : residue 𝒪 (a ℓ₁) = θ₀ (CuspForm.heckeAlgebra.T hℓ₁ hℓ₁N hℓ₁S') := by
      rw [ha ℓ₁ hℓ₁ hℓ₁S' hℓ₁N]
      exact IsLocalRing.residue_algHom_apply_eq_of_residue_eq_map πT₀ _ _
        (CuspForm.heckeLocal.residue_pi N (↑S : Set ℕ) 𝒪 θ₀ _)
    have hchar := hθ₀ ℓ₁ hℓ₁ hℓ₁N hℓ₁S' A₁ hA₁ σ₁ hσ₁
    rw [hchar] at heval
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, one_pow, mul_one] at heval

    by_contra hnu
    have hmem : a ℓ₁ - ((ℓ₁ : 𝒪) + 1) ∈ maximalIdeal 𝒪 := by
      simpa [mem_maximalIdeal, mem_nonunits_iff] using hnu
    have h0 : residue 𝒪 (a ℓ₁ - ((ℓ₁ : 𝒪) + 1)) = 0 := (residue_eq_zero_iff _).mpr hmem
    rw [map_sub, map_add, map_one, map_natCast, hres] at h0
    apply heval
    linear_combination (-1 : ResidueField 𝒪) * h0

  obtain ⟨x₀, hx₀T, hx₀ne⟩ := (Submodule.ne_bot_iff _).mp hocc₀
  obtain ⟨x₁, hx₁T, hx₁ne⟩ := (Submodule.ne_bot_iff _).mp hEocc
  have hx₀ne' : (x₀ : H1 (N * r) H₀ 𝒪) ≠ 0 := fun h => hx₀ne (Subtype.ext h)
  have hx₁ne' : (x₁ : H1 (N * r * p) H 𝒪) ≠ 0 := fun h => hx₁ne (Subtype.ext h)
  have hresT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓNr : ¬ ℓ ∣ N * r),
      a ℓ - cfull (CohCarrier.Gen.T ℓ hℓ hℓS hℓNr) ∈ maximalIdeal 𝒪 := by
    intro ℓ hℓ hℓS hℓNr
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓS₀ : ℓ ∉ S := by exact_mod_cast hℓS
    have hℓNrp : ¬ ℓ ∣ N * r * p := by
      intro h
      rcases hℓ.dvd_mul.mp h with h | h
      · exact hℓNr h
      · exact hℓS₀ (((Nat.prime_dvd_prime_iff_eq hℓ hpp).mp h) ▸ hpS)
    refine Rg6.sub_mem_maximalIdeal_of_smul_eq S₀ i₀ (tfull (CohCarrier.Gen.T ℓ hℓ hℓS hℓNr)) _ _
      (hcfull _ trivial) (x₀ : H1 (N * r) H₀ 𝒪) x₀.2 hx₀ne' ?_
    rw [htfull _ trivial]
    exact hE0T _ (hmkE0 x₀ hx₀T) ℓ hℓ hℓS₀ hℓNrp
  have hresU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
      cq q - cfull (CohCarrier.Gen.U q hq (hqN.mul_right r)) ∈ maximalIdeal 𝒪 := by
    intro q hq hqN
    haveI : NeZero q := ⟨hq.ne_zero⟩
    refine Rg6.sub_mem_maximalIdeal_of_smul_eq Sₐ iₐ (tA (CohCarrier.Gen.U q hq (hqN.mul_right r))) _ _
      (hEcf _ hqN) (x₁ : H1 (N * r * p) H 𝒪) (hEsub _ x₁.2) hx₁ne' ?_
    rw [← hι, hψact x₁ hx₁T, hcq q hq hqN]
  have hresD : ∀ d : (ZMod (N * r))ˣ, (1 : 𝒪) - cfull (CohCarrier.Gen.dia d) ∈ maximalIdeal 𝒪 := by
    intro d
    refine Rg6.sub_mem_maximalIdeal_of_smul_eq S₀ i₀ (tfull (CohCarrier.Gen.dia d)) _ _
      (hcfull _ trivial) (x₀ : H1 (N * r) H₀ 𝒪) x₀.2 hx₀ne' ?_
    rw [htfull _ trivial, one_smul]
    exact hdia _ _ x₀.2

  have hE0mem : ∀ m : H1 (N * r) H₀ 𝒪,
      (∀ σ : CongruenceSubgroup.Gamma0 (N * r), diamondRaw (N * r) H₀ 𝒪 σ m = m) →
      (∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * r → heckeT (N * r) H₀ ℓ 𝒪 m = a ℓ • m) →
      (∀ (q : ℕ) [NeZero q], q.Prime → q ∣ N → heckeT (N * r) H₀ q 𝒪 m = cq q • m) → m ∈ E0 := by
    intro m hmdia hmT hmq

    have hmM₀ : m ∈ M₀ := by
      apply hcofull
      intro g hg k
      obtain ⟨lam, hlam, hlamres⟩ : ∃ lam : 𝒪, tfull g • m = lam • m ∧ lam - cfull g ∈ maximalIdeal 𝒪 := by
        cases g with
        | T ℓ hℓ hℓS hℓNr =>
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          refine ⟨a ℓ, ?_, hresT ℓ hℓ hℓS hℓNr⟩
          rw [htfull _ hg]
          exact hmT ℓ hℓ (by exact_mod_cast hℓS) hℓNr
        | U q hq hqNr =>
          haveI : NeZero q := ⟨hq.ne_zero⟩
          refine ⟨cq q, ?_, hresU q hq hg⟩
          rw [htfull _ hg]
          exact hmq q hq hg
        | dia d =>
          refine ⟨1, ?_, hresD d⟩
          rw [htfull _ hg, one_smul]
          exact hmdia _
      refine ⟨k, ?_⟩
      have hpow : ∀ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋₀ (cfull g)) ^ n) • m = ((lam - cfull g) ^ n) • m := by
        intro n
        induction n with
        | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
        | succ n ih =>
          rw [pow_succ, mul_smul, sub_smul, hlam, algebraMap_smul, ← sub_smul, smul_comm, ih,
            smul_smul, ← pow_succ']
      rw [hpow k]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hlamres k) Submodule.mem_top

    set m' : ↥M₀ := ⟨m, hmM₀⟩ with hm'
    set S' : Finset ℕ := insert r S with hS'
    have hSS' : (↑S : Set ℕ) ⊆ (↑S' : Set ℕ) := by
      rw [hS', Finset.coe_insert]; exact Set.subset_insert _ _
    have hSS'f : S ⊆ S' := Finset.subset_insert r S
    let incl : ↥(CuspForm.heckeAlgebra N 2 (↑S' : Set ℕ)) →ₐ[ℤ] ↥(CuspForm.heckeAlgebra N 2 (↑S : Set ℕ)) :=
      Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hSS')
    set θ' : ↥(CuspForm.heckeAlgebra N 2 (↑S' : Set ℕ)) →+* ResidueField 𝒪 :=
      θ₀.comp incl.toRingHom with hθ'
    obtain ⟨Ψ, -, hΨ⟩ := CuspForm.heckeLocal.exists_algHom_of_subset N (↑S' : Set ℕ) (↑S : Set ℕ) hSS' 𝒪
      θ₀ θ' (fun t => rfl)
    have hΨbij := CuspForm.heckeLocal.bijective_of_subset_of_forall_prime_mem_of_charpoly_frobenius_eq
      p hp𝒪 ρbar habs S' S hpS hSS'f N hNS θ₀ hθ₀ θ' (fun t => rfl) Ψ hΨ
    have htop : Algebra.adjoin 𝒪 (Set.range (CuspForm.heckeLocal.π N (↑S' : Set ℕ) 𝒪 θ')) = ⊤ :=
      CuspForm.heckeLocal.adjoin_range_pi N (↑S' : Set ℕ) 𝒪 θ' Fact.out

    let ρ₀ : ↥(CuspForm.heckeAlgebra N 2 (↑S' : Set ℕ)) →+* S₀.CornerRing i₀ :=
      (e₀.symm : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] S₀.CornerRing i₀).toRingHom.comp
        ((CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀).comp incl.toRingHom)
    have hρ₀ : ∀ t, ρ₀ t = e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (incl t)) := fun t => rfl
    have hgen : ∀ c : S₀.CornerRing i₀, c ∈ Algebra.adjoin 𝒪 (Set.range ρ₀) := by
      intro c
      obtain ⟨y, hy⟩ := hΨbij.2 (e₀ c)
      have hy' : y ∈ Algebra.adjoin 𝒪 (Set.range (CuspForm.heckeLocal.π N (↑S' : Set ℕ) 𝒪 θ')) := by
        rw [htop]; exact Algebra.mem_top
      let F : CuspForm.heckeLocal N (↑S' : Set ℕ) 𝒪 θ' →ₐ[𝒪] S₀.CornerRing i₀ :=
        (e₀.symm : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] S₀.CornerRing i₀).comp Ψ
      have hF : F y = c := by
        show e₀.symm (Ψ y) = c
        rw [hy, AlgEquiv.symm_apply_apply]
      have hmem : F y ∈ (Algebra.adjoin 𝒪 (Set.range (CuspForm.heckeLocal.π N (↑S' : Set ℕ) 𝒪 θ'))).map F :=
        Subalgebra.mem_map.mpr ⟨y, hy', rfl⟩
      rw [hF, AlgHom.map_adjoin] at hmem
      refine Algebra.adjoin_mono ?_ hmem
      rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      refine ⟨t, ?_⟩
      show ρ₀ t = e₀.symm (Ψ _)
      rw [hΨ t, hρ₀]

    let Q : Subalgebra 𝒪 (S₀.CornerRing i₀) :=
      { carrier := {c | c • m' = χ₀ c • m'}
        mul_mem' := fun {c d} hc hd => by
          show (c * d) • m' = χ₀ (c * d) • m'
          calc (c * d) • m' = c • (d • m') := mul_smul c d m'
            _ = c • (χ₀ d • m') := by rw [show d • m' = χ₀ d • m' from hd]
            _ = c • (algebraMap 𝒪 (S₀.CornerRing i₀) (χ₀ d) • m') := by rw [algebraMap_smul]
            _ = (c * algebraMap 𝒪 (S₀.CornerRing i₀) (χ₀ d)) • m' := smul_smul c _ m'
            _ = (algebraMap 𝒪 (S₀.CornerRing i₀) (χ₀ d) * c) • m' := by rw [mul_comm c]
            _ = algebraMap 𝒪 (S₀.CornerRing i₀) (χ₀ d) • (c • m') :=
                mul_smul (algebraMap 𝒪 (S₀.CornerRing i₀) (χ₀ d)) c m'
            _ = χ₀ d • (c • m') := algebraMap_smul _ _ _
            _ = χ₀ d • (χ₀ c • m') := by rw [show c • m' = χ₀ c • m' from hc]
            _ = (χ₀ d * χ₀ c) • m' := smul_smul _ _ _
            _ = χ₀ (c * d) • m' := by rw [map_mul, mul_comm (χ₀ d) (χ₀ c)]
        one_mem' := by show (1 : S₀.CornerRing i₀) • m' = χ₀ 1 • m'; rw [one_smul, map_one, one_smul]
        add_mem' := fun {c d} hc hd => by
          show (c + d) • m' = χ₀ (c + d) • m'
          rw [add_smul, hc, hd, map_add, add_smul]
        zero_mem' := by
          show (0 : S₀.CornerRing i₀) • m' = χ₀ 0 • m'
          exact (zero_smul (S₀.CornerRing i₀) m').trans (by rw [map_zero, zero_smul])
        algebraMap_mem' := fun o => by
          show algebraMap 𝒪 (S₀.CornerRing i₀) o • m' = χ₀ (algebraMap 𝒪 (S₀.CornerRing i₀) o) • m'
          rw [algebraMap_smul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] }
    have hQρ : ∀ t, ρ₀ t ∈ Q := by
      intro t
      obtain ⟨t, ht⟩ := t
      refine Algebra.adjoin_induction (p := fun s hs => ρ₀ ⟨s, hs⟩ ∈ Q) ?_ ?_ ?_ ?_ ht
      ·
        rintro s hs
        rcases hs with ⟨ℓ, hℓ, hℓN, hℓS', rfl⟩ | ⟨q, hqN, hq, hqS', rfl⟩
        · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS' (hSS' h)
          have hℓr : ℓ ≠ r := by rintro rfl; exact hℓS' (by simp [hS'])
          have hℓNr : ¬ ℓ ∣ N * r := by
            intro h
            rcases hℓ.dvd_mul.mp h with h | h
            · exact hℓN h
            · exact hℓr ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp h)
          show ρ₀ _ • m' = χ₀ (ρ₀ _) • m'
          have e1 : ρ₀ ⟨CuspForm.heckeTLin 2 hℓ hℓN, CuspForm.heckeTLin_mem_heckeAlgebra hℓ hℓN hℓS'⟩ =
              e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := rfl
          rw [e1]
          apply Subtype.ext
          rw [Submodule.coe_smul_of_tower, hT₀ ℓ hℓ hℓN hℓS hℓNr m']
          show heckeT (N * r) H₀ ℓ 𝒪 m = _
          rw [hmT ℓ hℓ (by exact_mod_cast hℓS) hℓNr, ha ℓ hℓ hℓS hℓN]
          congr 1
          simp only [hχ₀, AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.apply_symm_apply]
        · exact absurd (hSS' (hNS q hq hqN)) hqS'
      · intro n
        have e : (⟨algebraMap ℤ _ n, Subalgebra.algebraMap_mem _ n⟩ :
            ↥(CuspForm.heckeAlgebra N 2 (↑S' : Set ℕ))) = algebraMap ℤ _ n := Subtype.ext rfl
        rw [e, eq_intCast, map_intCast]
        exact Subalgebra.intCast_mem Q n
      · intro s t hs' ht' hs ht
        have := Q.add_mem hs ht
        rwa [← map_add] at this
      · intro s t hs' ht' hs ht
        have := Q.mul_mem hs ht
        rwa [← map_mul] at this
    have hQall : ∀ c : S₀.CornerRing i₀, c • m' = χ₀ c • m' := by
      intro c
      have : c ∈ Q := (Algebra.adjoin_le (by rintro _ ⟨t, rfl⟩; exact hQρ t) : _ ≤ Q) (hgen c)
      exact this
    have hmT₀ : m' ∈ T₀ := by
      rw [hT₀def, Submodule.mem_torsionBySet_iff]
      rintro ⟨z, hz⟩
      rw [Subtype.coe_mk, hQall z, RingHom.mem_ker.mp hz, zero_smul]
    exact hmkE0 m' hmT₀

  have hfinal := Rg6.finrank_le_of_eigen_data p N r hpNr S hpS H₀ H h1 hp' h₁ₐ h1t hpt h₀ a u hu cq
    ℓ₁ hℓ₁ hℓ₁S hℓ₁Nrp hℓ₁mod hℓ₁unit E1 hE1par hE1T hE1U hE1q E0 hE0ne hE0T hE0dia hE0mem
  rw [hfin1, hfin0] at hfinal
  exact hfinal

end S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul
end P2MW
export P2MW.S_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul (solution)

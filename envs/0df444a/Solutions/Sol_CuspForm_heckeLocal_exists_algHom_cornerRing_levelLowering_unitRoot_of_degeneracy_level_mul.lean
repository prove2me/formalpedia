-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_algHom_cornerRing_levelLowering_unitRoot_of_degeneracy_level_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/311b3802-6c88-51c7-9549-f8bfc6b7f5e9

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_CohCarrier_isEis_kernel_pair_of_prime
import Theorems.Thm_CohCarrier_isEis_of_iDeg_add_eq_zero_of_diamond_invariant
import Theorems.Thm_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one
import Theorems.Thm_CohCarrier_index_comap_unitsMap
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
import Theorems.Thm_CuspForm_heckeLocal_exists_surjective_algHom_apply_pi_T_eq_of_dvd
import Theorems.Thm_AlgHom_exists_intertwiner_of_adjoin_eq_top_of_injective
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Theorems.Thm_CohCarrier_iDeg_diamondRaw_comm
import Theorems.Thm_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw
import Theorems.Thm_CohCarrier_heckeT_iDeg_q_eq_smul_r
import Theorems.Thm_CuspForm_heckeLocal_exists_algHom_of_subset
import Theorems.Thm_CuspForm_heckeLocal_bijective_of_subset_of_forall_prime_mem_of_charpoly_frobenius_eq
import Theorems.Thm_CuspForm_heckeLocal_adjoin_range_pi
import Theorems.Thm_CuspForm_heckeAlgebra_ringHom_ext_of_primeFactors_subset
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Theorems.Thm_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_algHom_cornerRing_levelLowering_unitRoot_of_degeneracy_level_mul
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois Deformation.ProartinianCat.instCategory Deformation.ProartinianCat.topologicalSpace Deformation.ProartinianCat.instUniqueHomSelf Deformation.IsLocalProartinianAlgebra.toIsLocalHom Deformation.ProartinianCat.instDiscreteTopologyCarrierResidueField Deformation.ProartinianCat.algebra Deformation.IsLocalProartinianAlgebra.toIsLocalRing Deformation.IsLocalProartinianAlgebra.toIsProartinian Deformation.IsLocalProartinianAlgebra.toIsTopologicalRing Deformation.ProartinianCat.instCoeSortType Deformation.ProartinianCat.instUniqueHomResidueField Deformation.ProartinianCat.instIsLocalHomCarrierContinuousAlgHomHom Deformation.IsLocalProartinianAlgebra.toIsResidueAlgebra Deformation.ProartinianCat.isLocalProartinianAlgebra Deformation.ProartinianCat.instIsAdicTopologyCarrierSelf Deformation.ProartinianCat.commRing Deformation.ProartinianCat.instFieldCarrierResidueField IsLocalRing.instDiscreteTopologyQuotientIdealHPowNatMaximalIdeal_definitions IsLocalRing.instIsLinearTopology_definitions IsProartinian.toT0Space instIsProartinianOfDiscreteTopologyOfIsArtinianRing IsLocalRing.instIsAdicTopology instIsProartinianOfIsAdicTopologyOfIsNoetherianRingOfCompactSpace IsLocalRing.instIsHausdorffMaximalIdealOfIsNoetherianRing_definitions IsLocalRing.instNonarchimedeanRing_definitions IsLocalRing.instIsPrecompleteMaximalIdealOfCompactSpace_definitions IsLocalRing.instDiscreteTopologyOfIsArtinianRing_definitions IsLocalRing.instT2SpaceOfIsNoetherianRing_definitions IsProartinian.toCompleteSpace IsProartinian.toIsLinearTopology instTopologicallyFGOfFiniteType instMulSemiringActionSubtypeMemIntermediateFieldOfSMulCommClassOfNormal_definitions instIsLocalHomRingHomAlgebraMap_definitions instContinuousConstSMulConjActOfContinuousMul_definitions instIsLocalHomRingHomToRingHom_definitions_1"
p2m_attr_erase "instance" "instIsLocalHomResidueFieldRingHomAlgebraMap_definitions instMulSemiringActionRingOfIntegers_definitions instIsLocalHomRingHomToRingHom_definitions instMulActionContinuousMonoidHomOfContinuousConstSMul_definitions instFiniteIndexMulOppositeOp_definitions ValuationSubring.smulCommClass instFaithfulSMulSubtypeMemValuationSubring_definitions ContinuousAlgHom.isLocalHom_id instIsModuleTopologyMatrixOfFiniteOfIsTopologicalRing_definitions IsTopologicalAddGroup.discreteUniformity IntermediateField.smulCommClass_of_normal instMulActionMonoidHomOfMulDistribMulAction_definitions IsTopologicalGroup.discreteUniformity instIsLocalHomRingHomOfContinuousAlgHom_definitions Additive.instDistrbMulAction instIsLocalHomRingHomOfContinuousAlgHom_definitions_1 instNumberFieldSubtypeMemIntermediateFieldOfFiniteDimensional_definitions ContinuousAlgHom.isLocalHom_comp instIsLocalHomContinuousAlgHomToContinuousAlgHom_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsResidueAlgebra.inst IsResidueAlgebra.instQuotientIdeal IsLocalRing.quot IsLocalHom.quotient_mk Deformation.ProartinianCat.ClosedSubalgebra.instNontrivialSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsLinearTopologySubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsTopologicalRingSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace TateModule.instModule TateModule.instSMul ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "instance" "ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat Deformation.ProartinianCat.Hom.mk.injEq Deformation.ProartinianCat.ofHom_comp Deformation.ProartinianCat.hom_comp Deformation.ProartinianCat.mk.sizeOf_spec Deformation.ProartinianCat.Hom.mk.sizeOf_spec Deformation.ProartinianCat.ofEquiv_hom_hom Deformation.ProartinianCat.ofHom_id"
p2m_attr_erase "simp" "Deformation.ProartinianCat.hom_id Deformation.ProartinianCat.ofEquiv_inv_hom Deformation.ProartinianCat.mk.injEq Deformation.ProartinianCat.ofHom_hom ContinuousMonoidHom.val_inv_toHomUnits_toFun Units.val_mapₜ_toFun MonoidHom.coe_smul ContinuousAlgHom.coe_toContinuousMonoidHom ContinuousMonoidHom.val_toHomUnits_toFun ContinuousMonoidHom.mk_toMonoidHom ContinuousAlgHom.mapMatrix_apply Units.val_inv_mapₜ_toFun Units.coeHomₜ_toFun ContinuousMonoidHom.coe_mk ContinuousMonoidHom.coe_smul AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom Deformation.repnFunctor_map Deformation.mapRepn_apply Deformation.ProartinianCat.closedSubalgebraι_apply Deformation.matrixRepresentation_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id"
p2m_attr_erase "simp" "ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply"
p2m_attr_erase "simp" "AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff CuspForm.coe_heckeULowerLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_traceLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower
open scoped MatrixGroups

namespace PsiStubR

theorem stab_injective
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (r : ℕ) (hr : r.Prime) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (H₀ : Subgroup (ZMod (N * r))ˣ) [NeZero (N * r)]
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1)
    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 (N * r) H₀ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 (N * r) H₀ 𝒪)]
    (S₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin S₀.n)
    (e₀ : S₀.CornerRing i₀ ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
    (hT₀ : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r)
        (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))),
      ((e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
          : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ ℓ 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (hdia : ∀ (σ : ↥(CongruenceSubgroup.Gamma0 (N * r))) (v : H1 (N * r) H₀ 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) → diamondRaw (N * r) H₀ 𝒪 σ v = v)
    [NeZero (N * r * p)]
    (h1 : LevelLE (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 1)
    (hp' : LevelLE (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p)
    (αt : S₀.CornerRing i₀)
    (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)))
    (hm : iDegL (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 1 𝒪 𝒪 h1
        ((αt • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪)
      - iDegL (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p 𝒪 𝒪 hp' (m : H1 (N * r) H₀ 𝒪) = 0) :
    m = 0 := by
  classical
  set H : Subgroup (ZMod (N * r * p))ˣ := H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)) with hHdef
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hprN : ¬ p ∣ N * r := by
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp h with h | h
    · exact hpN h
    · have : p = r := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).mp h
      exact hrN (this ▸ dvd_mul_left p N)
  have hNr0 : 0 < N * r := Nat.pos_of_ne_zero (NeZero.ne _)
  have hNrp0 : 0 < N * r * p := Nat.pos_of_ne_zero (NeZero.ne _)

  have h₁top : LevelLE (N * r) (N * r * p) (⊤ : Subgroup (ZMod (N * r))ˣ) (⊤ : Subgroup (ZMod (N * r * p))ˣ) 1 :=
    ⟨dvd_mul_right _ _, one_dvd _, fun u _ => Subgroup.mem_top _⟩
  have hqtop : LevelLE (N * r) (N * r * p) (⊤ : Subgroup (ZMod (N * r))ˣ) (⊤ : Subgroup (ZMod (N * r * p))ˣ) p :=
    ⟨dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left p hNr0], fun u _ => Subgroup.mem_top _⟩
  haveI : NeZero (N * r * p * p) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne p)⟩
  have h₁top' : LevelLE (N * r * p) (N * r * p * p) (⊤ : Subgroup (ZMod (N * r * p))ˣ) (⊤ : Subgroup (ZMod (N * r * p * p))ˣ) 1 :=
    ⟨dvd_mul_right _ _, one_dvd _, fun u _ => Subgroup.mem_top _⟩
  have hqtop' : LevelLE (N * r * p) (N * r * p * p) (⊤ : Subgroup (ZMod (N * r * p))ˣ) (⊤ : Subgroup (ZMod (N * r * p * p))ˣ) p :=
    ⟨dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left p hNrp0], fun u _ => Subgroup.mem_top _⟩

  have hunit : IsUnit ((H₀.index : ℕ) : 𝒪) :=
    CohCarrier.isUnit_index_of_forall_mem_iff_castHom_eq_one p hp𝒪 N r hr hr1 H₀ hH₀
  have hunit' : IsUnit ((H.index : ℕ) : 𝒪) := by
    rw [hHdef, CohCarrier.index_comap_unitsMap]; exact hunit

  have hM0 : 0 < N * r * p * ∏ q ∈ S, q :=
    Nat.pos_of_ne_zero (Nat.mul_ne_zero (NeZero.ne _)
      (Finset.prod_ne_zero_iff.mpr (fun q hq => (hS q hq).ne_zero)))
  obtain ⟨ℓ₀, A, σ, hℓ₀, hℓ₀M, -, hA, hσ, hev⟩ :=
    ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_eval_charpoly_ne_zero_of_isAbsolutelyIrreducible
      ρbar habs 1 hM0
  have hℓ₀Nrp : ¬ ℓ₀ ∣ N * r * p := fun h => hℓ₀M (h.mul_right _)
  have hℓ₀Nr : ¬ ℓ₀ ∣ N * r := fun h => hℓ₀Nrp (h.mul_right _)
  have hℓ₀N : ¬ ℓ₀ ∣ N := fun h => hℓ₀Nr (h.mul_right _)
  have hℓ₀S : ℓ₀ ∉ (↑S : Set ℕ) := fun h =>
    hℓ₀M ((Finset.dvd_prod_of_mem (fun q => q) (Finset.mem_coe.mp h)).trans (dvd_mul_left _ _))
  haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩

  have hne : θ₀ (CuspForm.heckeAlgebra.T hℓ₀ hℓ₀N hℓ₀S) ≠ (ℓ₀ : ResidueField 𝒪) + 1 := by
    intro heq
    apply hev
    rw [hθ₀ ℓ₀ hℓ₀ hℓ₀N hℓ₀S A hA σ hσ, heq]
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

  have hihara_top := (CohCarrier.isEis_kernel_pair_of_prime 𝒪 𝒪 ℓ₀ (N * r) p h₁top hqtop h₁top' hqtop'
    (Fact.out : p.Prime) hprN hℓ₀ hℓ₀Nrp).1
  set g : H1 (N * r) H₀ 𝒪 := ((αt • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) with hgdef
  set h : H1 (N * r) H₀ 𝒪 := -(m : H1 (N * r) H₀ 𝒪) with hhdef
  have hg : ∀ τ : CongruenceSubgroup.Gamma0 (N * r), diamondRaw (N * r) H₀ 𝒪 τ g = g :=
    fun τ => hdia τ g (αt • m).2
  have hh : ∀ τ : CongruenceSubgroup.Gamma0 (N * r), diamondRaw (N * r) H₀ 𝒪 τ h = h := by
    intro τ
    rw [hhdef, map_neg, hdia τ _ m.2]
  have hgh : iDeg' (N * r) (N * r * p) H₀ H 1 𝒪 h1 g + iDeg' (N * r) (N * r * p) H₀ H p 𝒪 hp' h = 0 := by
    rw [hhdef, map_neg, ← sub_eq_add_neg]
    exact hm
  have hEis := (CohCarrier.isEis_of_iDeg_add_eq_zero_of_diamond_invariant 𝒪 𝒪 ℓ₀ (N * r) p H₀ H h1 hp'
    h₁top hqtop hℓ₀ hℓ₀Nrp hunit hunit' hihara_top g h hg hh hgh).2

  have hTm : heckeT (N * r) H₀ ℓ₀ 𝒪 (m : H1 (N * r) H₀ 𝒪) = ((ℓ₀ : 𝒪) + 1) • (m : H1 (N * r) H₀ 𝒪) := by
    have := hEis
    rw [CohCarrier.IsEis, hhdef, map_neg, smul_neg, neg_inj] at this
    exact this

  set t : S₀.CornerRing i₀ := e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ₀ hℓ₀N hℓ₀S)) with htdef
  have hkill : ((t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) • m
      : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) = 0 := by
    have hsub : (t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) • m =
        t • m - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1) • m :=
      sub_smul t (algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) m
    have halg : algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1) • m = ((ℓ₀ : 𝒪) + 1) • m :=
      algebraMap_smul (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1) m
    rw [hsub, halg, sub_eq_zero]
    apply Subtype.ext
    rw [hT₀ ℓ₀ hℓ₀ hℓ₀N hℓ₀S hℓ₀Nr m, hTm]
    exact (Submodule.coe_smul_of_tower _ _).symm

  have hunit_t : IsUnit (t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) := by
    have himg : e₀ (t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1)) =
        CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ₀ hℓ₀N hℓ₀S)
          - algebraMap 𝒪 _ ((ℓ₀ : 𝒪) + 1) := by
      rw [map_sub, htdef, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    suffices hu : IsUnit (e₀ (t - algebraMap 𝒪 (S₀.CornerRing i₀) ((ℓ₀ : 𝒪) + 1))) by
      simpa using hu.map e₀.symm
    rw [himg]
    by_contra hnu
    have hmem := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hres := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sub, CuspForm.heckeLocal.residue_pi, ← IsLocalRing.ResidueField.map_residue, ← map_sub,
      map_eq_zero_iff _ (RingHom.injective _), map_add, map_natCast, map_one, sub_eq_zero] at hres
    exact hne hres
  exact (hunit_t.smul_left_cancel).mp (by rw [hkill, smul_zero])

theorem heckeT_stab_eq_stab_smul
    {𝒪 : Type} [CommRing 𝒪]
    (M q : ℕ) [NeZero M] [NeZero q] [NeZero (M * q)]
    (Hs : Subgroup (ZMod M)ˣ) (Hs' : Subgroup (ZMod (M * q))ˣ)
    (h1 : LevelLE M (M * q) Hs Hs' 1) (hq' : LevelLE M (M * q) Hs Hs' q)
    {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M Hs 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M Hs 𝒪)]
    (S₀ : IdempotentSplitting 𝕋) (i₀ : Fin S₀.n)
    (tp αt : S₀.CornerRing i₀)
    (hquad : αt * αt - tp * αt + algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪) = 0)
    (hTp : ∀ m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) = heckeT M Hs q 𝒪 (m : H1 M Hs 𝒪))
    (hdia : ∀ (σ : ↥(CongruenceSubgroup.Gamma0 M)) (v : H1 M Hs 𝒪),
      v ∈ cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀) → diamondRaw M Hs 𝒪 σ v = v)
    (σ : ↥(CongruenceSubgroup.Gamma0 M))
    (hU1 : ∀ v : H1 M Hs 𝒪, heckeT (M * q) Hs' q 𝒪 (iDeg' M (M * q) Hs Hs' 1 𝒪 h1 v) =
      iDeg' M (M * q) Hs Hs' 1 𝒪 h1 (heckeT M Hs q 𝒪 v) - iDeg' M (M * q) Hs Hs' q 𝒪 hq' (diamondRaw M Hs 𝒪 σ v))
    (hUq : ∀ v : H1 M Hs 𝒪, heckeT (M * q) Hs' q 𝒪 (iDeg' M (M * q) Hs Hs' q 𝒪 hq' v) =
      q • iDeg' M (M * q) Hs Hs' 1 𝒪 h1 v)
    (m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) :
    heckeT (M * q) Hs' q 𝒪
        (iDegL M (M * q) Hs Hs' 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
          - iDegL M (M * q) Hs Hs' q 𝒪 𝒪 hq' (m : H1 M Hs 𝒪)) =
      iDegL M (M * q) Hs Hs' 1 𝒪 𝒪 h1 ((αt • (αt • m) : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪)
        - iDegL M (M * q) Hs Hs' q 𝒪 𝒪 hq' ((αt • m : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) := by

  have hL1 : ∀ v : H1 M Hs 𝒪, iDegL M (M * q) Hs Hs' 1 𝒪 𝒪 h1 v = iDeg' M (M * q) Hs Hs' 1 𝒪 h1 v := fun v => rfl
  have hLq : ∀ v : H1 M Hs 𝒪, iDegL M (M * q) Hs Hs' q 𝒪 𝒪 hq' v = iDeg' M (M * q) Hs Hs' q 𝒪 hq' v := fun v => rfl
  simp only [hL1, hLq]
  rw [map_sub, hU1, hUq, hdia σ _ (αt • m).2, ← hTp (αt • m)]

  have hquad' : αt * αt = tp * αt - algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪) := by
    rw [← sub_eq_zero, ← hquad]; ring
  have hq2 : ((αt • (αt • m) : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) =
      ((tp • (αt • m) : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (S₀.e i₀))) : H1 M Hs 𝒪) - q • (m : H1 M Hs 𝒪) := by
    have h3 : αt • (αt • m) = tp • (αt • m) - algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪) • m := by
      rw [← mul_smul αt αt m, ← mul_smul tp αt m, hquad']
      exact sub_smul (tp * αt) (algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪)) m
    have h4 : algebraMap 𝒪 (S₀.CornerRing i₀) (q : 𝒪) • m = (q : 𝒪) • m :=
      algebraMap_smul (S₀.CornerRing i₀) (q : 𝒪) m
    rw [h3, h4, Submodule.coe_sub, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
  rw [hq2, map_sub, map_nsmul]
  abel

end PsiStubR

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
    ∃ res₁ : S₁.CornerRing i₁ →ₐ[𝒪] S₀.CornerRing i₀,
      Function.Surjective res₁ ∧
      πT₁.comp e₁.toAlgHom = (πT₀.comp e₀.toAlgHom).comp res₁ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓNp : ¬ ℓ ∣ N * p) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        res₁ (e₁.symm (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓNp hℓS))) =
          e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) ∧
      res₁ (S₁.toCornerRing i₁ U) = αt ∧
      Module.finrank 𝒪 ((Submodule.torsionBySet (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))
          ↑(RingHom.ker (πT₁.comp e₁.toAlgHom))).restrictScalars 𝒪) =
        Module.finrank 𝒪 ((Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
          ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))).restrictScalars 𝒪) ∧

      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ N * r), q ∣ N →
        ∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
          ((res₁ (S₁.toCornerRing i₁ (ι (tA (.U q hq hqM)))) • m
              : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) =
            (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT (N * r) H₀ q 𝒪 (m : H1 (N * r) H₀ 𝒪)))
 := by
  classical
  have hE' := hE
  obtain ⟨hEa, hEb, hEc, hEd, hEe, hE4, hcomap, hUm, hordα, href, ⟨φ, hφsurj, hφact, hTe₁⟩, hfaith₁, hocc₁, hrk₁, hsat₁⟩ := hE
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hSNp : ∀ q : ℕ, q.Prime → q ∣ N * p → q ∈ (↑S : Set ℕ) := by
    intro q hq hqNp
    rcases (Nat.Prime.dvd_mul hq).mp hqNp with h | h
    · exact hNS q hq h
    · rw [(Nat.prime_dvd_prime_iff_eq hq Fact.out).mp h]; exact hpS
  have hθ01 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓNp : ¬ ℓ ∣ N * p) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      θ₁ (CuspForm.heckeAlgebra.T hℓ hℓNp hℓS) =
        θ₀ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓNp (h.trans (dvd_mul_right N p))) hℓS) := by
    intro ℓ hℓ hℓNp hℓS
    obtain ⟨A, σ, hA, hσ⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨ℓ, hℓ⟩
    have h1 := hθ₁ ℓ hℓ hℓNp hℓS A hA σ hσ
    have h0 := hθ₀ ℓ hℓ (fun h => hℓNp (h.trans (dvd_mul_right N p))) hℓS A hA σ hσ
    have := h1.symm.trans h0

    have hc := congrArg (fun q : (ResidueField 𝒪)[X] => q.coeff 1) this
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X_one, coeff_C, if_neg (by decide : (1 : ℕ) ≠ 2),
      if_neg (one_ne_zero), mul_one] at hc
    simpa using hc
  obtain ⟨Ψ, hΨsurj, hΨT, hΨuniq⟩ :=
    CuspForm.heckeLocal.exists_surjective_algHom_apply_pi_T_eq_of_dvd (𝒪 := 𝒪) (↑S : Set ℕ) N (N * p)
      (dvd_mul_right N p) hSNp θ₀ θ₁ hθ01
  let res₁ : S₁.CornerRing i₁ →ₐ[𝒪] S₀.CornerRing i₀ :=
    (e₀.symm : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] S₀.CornerRing i₀).comp
      (Ψ.comp (e₁ : S₁.CornerRing i₁ →ₐ[𝒪] CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁))
  have hres₁ : ∀ x, res₁ x = e₀.symm (Ψ (e₁ x)) := fun x => rfl

  have hπΨ : πT₁ = πT₀.comp Ψ :=
    hΨuniq 𝒪 πT₀ πT₁ (fun ℓ hℓ hℓNp hℓS => hπ ℓ hℓ hℓS hℓNp (fun h => hℓNp (h.trans (dvd_mul_right N p))))
  have hconj2 : πT₁.comp e₁.toAlgHom = (πT₀.comp e₀.toAlgHom).comp res₁ := by
    ext x
    show πT₁ (e₁ x) = πT₀ (e₀ (e₀.symm (Ψ (e₁ x))))
    rw [AlgEquiv.apply_symm_apply, hπΨ, AlgHom.comp_apply]
  have hconj1 : Function.Surjective res₁ :=
    e₀.symm.surjective.comp (hΨsurj.comp e₁.surjective)
  have hconj3 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓNp : ¬ ℓ ∣ N * p) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      res₁ (e₁.symm (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓNp hℓS))) =
        e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := by
    intro ℓ hℓ hℓNp hℓN hℓS
    rw [hres₁, AlgEquiv.apply_symm_apply, hΨT ℓ hℓ hℓNp hℓS]

  set H : Subgroup (ZMod (N * r * p))ˣ := H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)) with hHdef
  subst hH
  let M₀ := ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
  let M₁ := ↥(cornerSubmodule (M := H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪) (S₁.e i₁))
  let stab : M₀ → H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪 := fun m =>
    iDegL (N * r) (N * r * p) H₀ _ 1 𝒪 𝒪 h1 ((αt • m : M₀) : H1 (N * r) H₀ 𝒪)
      - iDegL (N * r) (N * r * p) H₀ _ p 𝒪 𝒪 hp' (m : H1 (N * r) H₀ 𝒪)
  have hstab_add : ∀ m m' : M₀, stab (m + m') = stab m + stab m' := by
    intro m m'
    show iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • (m + m') : M₀) : H1 (N * r) H₀ 𝒪) - iDegL _ _ _ _ p 𝒪 𝒪 hp' ((m + m' : M₀) : H1 (N * r) H₀ 𝒪) = _
    rw [smul_add, Submodule.coe_add, Submodule.coe_add, map_add, map_add]
    show _ = (iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • m : M₀) : H1 (N * r) H₀ 𝒪) - iDegL _ _ _ _ p 𝒪 𝒪 hp' (m : H1 (N * r) H₀ 𝒪)) +
      (iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • m' : M₀) : H1 (N * r) H₀ 𝒪) - iDegL _ _ _ _ p 𝒪 𝒪 hp' (m' : H1 (N * r) H₀ 𝒪))
    abel
  have hαc : ∀ (c : 𝒪) (m : M₀), αt • (c • m) = c • (αt • m) := by
    intro c m
    rw [← algebraMap_smul (S₀.CornerRing i₀) c m, ← mul_smul αt (algebraMap 𝒪 (S₀.CornerRing i₀) c) m, mul_comm αt (algebraMap 𝒪 (S₀.CornerRing i₀) c),
      mul_smul (algebraMap 𝒪 (S₀.CornerRing i₀) c) αt m, algebraMap_smul]
  have hstab_smul : ∀ (c : 𝒪) (m : M₀), stab (c • m) = c • stab m := by
    intro c m
    show iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • (c • m) : M₀) : H1 (N * r) H₀ 𝒪) - iDegL _ _ _ _ p 𝒪 𝒪 hp' ((c • m : M₀) : H1 (N * r) H₀ 𝒪) =
      c • (iDegL _ _ _ _ 1 𝒪 𝒪 h1 ((αt • m : M₀) : H1 (N * r) H₀ 𝒪) - iDegL _ _ _ _ p 𝒪 𝒪 hp' (m : H1 (N * r) H₀ 𝒪))
    rw [hαc, Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, map_smul, map_smul, smul_sub]
  let iα : M₀ →ₗ[𝒪] M₁ :=
    { toFun := fun m => ⟨stab m, hLc m⟩
      map_add' := fun m m' => Subtype.ext (hstab_add m m')
      map_smul' := fun c m => Subtype.ext (hstab_smul c m) }
  have hiα : ∀ m : M₀, ((iα m : M₁) : H1 (N * r * p) _ 𝒪) = stab m := fun m => rfl
  have hiα_inj : Function.Injective iα := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    have hm' : stab m = 0 := by
      have := congrArg (fun x : M₁ => (x : H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪)) hm
      simpa [hiα] using this
    exact PsiStubR.stab_injective p hp𝒪 ρbar habs S hS N hpN r hr hrN hr1 θ₀ hθ₀ H₀ hH₀ S₀ i₀ e₀
      (fun ℓ _ hℓ hℓN hℓS hℓr m => hT₀ ℓ hℓ hℓN hℓS hℓr m) hdia h1 hp' αt m hm'

  let V₁ := H1 (N * r * p) (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 𝒪
  let Gₐ : Set 𝕋ₐ := tA '' {g | (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False)} ∪ Set.range dA
  have hGₐ : Algebra.adjoin 𝒪 Gₐ = ⊤ := hEe
  have hG₁ : Algebra.adjoin 𝒪 (ι '' Gₐ ∪ {U}) = ⊤ := by
    rw [← top_le_iff, ← hgen₁]
    refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      have ha : ι a ∈ (Algebra.adjoin 𝒪 Gₐ).map ι := ⟨a, by rw [hGₐ]; exact Algebra.mem_top, rfl⟩
      rw [← Algebra.adjoin_image] at ha
      exact Algebra.adjoin_mono Set.subset_union_left ha
    · exact Set.singleton_subset_iff.mpr (Algebra.subset_adjoin (Set.mem_union_right _ rfl))
  let tc : 𝕋₁ →ₐ[𝒪] S₁.CornerRing i₁ :=
    { toRingHom := S₁.toCornerRing i₁, commutes' := fun c => rfl }
  have htc : ∀ x, tc x = S₁.toCornerRing i₁ x := fun x => rfl
  have htc_surj : Function.Surjective tc := fun z =>
    ⟨(z : 𝕋₁), Subtype.ext (by rw [htc, IdempotentSplitting.coe_toCornerRing, S₁.e_mul_coe, S₁.coe_mul_e])⟩
  let G : Set (S₁.CornerRing i₁) := tc '' (ι '' Gₐ ∪ {U})
  have hG : Algebra.adjoin 𝒪 G = ⊤ := by
    show Algebra.adjoin 𝒪 (tc '' (ι '' Gₐ ∪ {U})) = ⊤
    rw [Algebra.adjoin_image, hG₁, Algebra.map_top, AlgHom.range_eq_top]
    exact htc_surj

  have htc_smul : ∀ (x : 𝕋₁) (m₁ : M₁), ((tc x • m₁ : M₁) : V₁) = S₁.e i₁ • (x • (m₁ : V₁)) := by
    intro x m₁
    rw [IdempotentSplitting.coe_cornerSmul, htc, IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul,
      S₁.e_smul_coe]
  have he_of_mem : ∀ v : V₁, v ∈ cornerSubmodule (M := V₁) (S₁.e i₁) → S₁.e i₁ • v = v :=
    fun v hv => S₁.e_smul_coe i₁ ⟨v, hv⟩

  have hL1 : ∀ v : H1 (N * r) H₀ 𝒪, iDegL (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) 1 𝒪 𝒪 h1 v =
      iDeg' (N * r) (N * r * p) H₀ _ 1 𝒪 h1 v := fun _ => rfl
  have hLp : ∀ v : H1 (N * r) H₀ 𝒪, iDegL (N * r) (N * r * p) H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) p 𝒪 𝒪 hp' v =
      iDeg' (N * r) (N * r * p) H₀ _ p 𝒪 hp' v := fun _ => rfl
  have hstab_def : ∀ m : M₀, stab m = iDeg' (N * r) (N * r * p) H₀ _ 1 𝒪 h1 ((αt • m : M₀) : H1 (N * r) H₀ 𝒪)
      - iDeg' (N * r) (N * r * p) H₀ _ p 𝒪 hp' (m : H1 (N * r) H₀ 𝒪) := fun _ => rfl
  have hcommC₀ : ∀ (y₀ : S₀.CornerRing i₀) (m : M₀), y₀ • (αt • m) = αt • (y₀ • m) := fun y₀ m => by
    rw [← mul_smul y₀ αt m, mul_comm y₀ αt, mul_smul αt y₀ m]
  have hpNr : ¬ p ∣ N * r := by
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · exact hpN h
    · exact hrN (((Nat.prime_dvd_prime_iff_eq Fact.out hr).mp h) ▸ dvd_mul_left p N)

  have hHc : ∀ u : (ZMod (N * r * p))ˣ, u ∈ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) ↔
      ZMod.castHom (dvd_mul_of_dvd_left (dvd_mul_left r N) p) (ZMod r) (u : ZMod (N * r * p)) = 1 := by
    intro u
    rw [Subgroup.mem_comap, hH₀, ZMod.unitsMap_val, ← ZMod.castHom_apply (h := dvd_mul_right (N * r) p)
      (R := ZMod (N * r)), ← RingHom.comp_apply, ZMod.castHom_comp]
  have hr4 : 4 ≤ r := le_trans (by norm_num) hr5
  obtain ⟨σ, -, hσ⟩ := CohCarrier.exists_gamma0_heckeT_iDeg_interchange_diamondRaw (N := N * r) (q := p)
    (A := 𝒪) Fact.out hpNr H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) h1 hp'
  have hUq : ∀ v : H1 (N * r) H₀ 𝒪, heckeT (N * r * p) _ p 𝒪 (iDeg' (N * r) (N * r * p) H₀ _ p 𝒪 hp' v) =
      p • iDeg' (N * r) (N * r * p) H₀ _ 1 𝒪 h1 v :=
    fun v => CohCarrier.heckeT_iDeg_q_eq_smul_r (N := N * r) (q := p) (A := 𝒪) r (dvd_mul_left r N) hr4
      H₀ hH₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p))) hHc h1 hp' v

  have hT1 : LevelLE (N * r) (N * r * p) (⊤ : Subgroup (ZMod (N * r))ˣ) (⊤ : Subgroup (ZMod (N * r * p))ˣ) 1 :=
    ⟨dvd_mul_right _ _, one_dvd _, fun _ _ => Subgroup.mem_top _⟩
  have hTp : LevelLE (N * r) (N * r * p) (⊤ : Subgroup (ZMod (N * r))ˣ) (⊤ : Subgroup (ZMod (N * r * p))ˣ) p :=
    ⟨dvd_mul_right _ _, by rw [Nat.mul_div_cancel_left p (NeZero.pos (N * r))], fun _ _ => Subgroup.mem_top _⟩
  have hdiam_stab : ∀ (d : (ZMod (N * r * p))ˣ) (m : M₀), diamondL (N * r * p) _ 𝒪 d (stab m) = stab m := by
    intro d m
    obtain ⟨σ', hσ'⟩ := CohCarrier.gamma0Units_surjective (N * r * p) d
    have hσ'T : (σ' : SL(2, ℤ)) ∈ GammaH (N * r * p) ⊤ := by rw [CohCarrier.GammaH_top]; exact σ'.2
    have hmem1 := hT1.conjLowerMat_mem ⟨(σ' : SL(2, ℤ)), hσ'T⟩
    have hmemp := hTp.conjLowerMat_mem ⟨(σ' : SL(2, ℤ)), hσ'T⟩
    rw [CohCarrier.GammaH_top] at hmem1 hmemp
    rw [hstab_def, map_sub, CohCarrier.diamondL_eq_diamondRaw (N * r * p) _ 𝒪 d σ' hσ',
      ← CohCarrier.iDeg_diamondRaw_comm h1 σ' (hT1.dvd_entry ⟨_, hσ'T⟩) ⟨_, hmem1⟩ rfl _,
      CohCarrier.diamondL_eq_diamondRaw (N * r * p) _ 𝒪 d σ' hσ',
      ← CohCarrier.iDeg_diamondRaw_comm hp' σ' (hTp.dvd_entry ⟨_, hσ'T⟩) ⟨_, hmemp⟩ rfl _,
      hdia ⟨_, hmem1⟩ _ (αt • m).2, hdia ⟨_, hmemp⟩ _ m.2]

  have htc₀_smul : ∀ (x : 𝕋₀) (m : M₀), ((S₀.toCornerRing i₀ x • m : M₀) : H1 (N * r) H₀ 𝒪) = x • (m : H1 (N * r) H₀ 𝒪) := by
    intro x m
    rw [IdempotentSplitting.coe_cornerSmul, IdempotentSplitting.coe_toCornerRing, mul_smul, mul_smul, S₀.e_smul_coe]
    exact S₀.e_smul_coe i₀ ⟨x • (m : H1 (N * r) H₀ 𝒪), Submodule.smul_mem _ x m.2⟩
  have hpartV : ∀ g ∈ G, ∃ y₀ : S₀.CornerRing i₀, ∀ m : M₀, ((g • iα m : M₁) : V₁) = stab (y₀ • m) := by
    rintro g ⟨x, hx, rfl⟩
    rcases hx with ⟨a, ha, rfl⟩ | hxU
    · rcases ha with ⟨g₀, hg₀, rfl⟩ | ⟨d, rfl⟩
      · cases g₀ with
        | T ℓ hℓ hℓS hℓM =>
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          have hℓN : ¬ ℓ ∣ N := fun h => hℓM (h.mul_right r)
          have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hpS)
          have hℓNrp : ¬ ℓ ∣ N * r * p := by
            intro h
            rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
            · exact hℓM h
            · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h)
          have hcop : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ Fact.out).mpr hℓp
          refine ⟨e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)), fun m => ?_⟩
          rw [htc_smul, hiα, hι, hEa _ trivial]
          have hval : heckeT (N * r * p) _ ℓ 𝒪 (stab m) =
              stab (e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m) := by
            rw [hstab_def, hstab_def, map_sub, ← CohCarrier.iDeg_heckeT_comm_of_coprime h1 (Nat.coprime_one_right ℓ) hℓ hℓNrp,
              ← CohCarrier.iDeg_heckeT_comm_of_coprime hp' hcop hℓ hℓNrp, ← hT₀ ℓ hℓ hℓN hℓS hℓM m,
              ← hT₀ ℓ hℓ hℓN hℓS hℓM (αt • m), hcommC₀]
          show S₁.e i₁ • heckeT (N * r * p) _ ℓ 𝒪 (stab m) = _
          rw [hval]
          exact he_of_mem _ (hLc _)
        | U q hq hqM =>
          haveI : NeZero q := ⟨hq.ne_zero⟩
          have hqN : q ∣ N := hg₀
          have hqp : q ≠ p := fun h => hpN (h ▸ hqN)
          have hcop : Nat.Coprime q p := (Nat.coprime_primes hq Fact.out).mpr hqp
          refine ⟨S₀.toCornerRing i₀ (tfull (.U q hq hqM)), fun m => ?_⟩
          have hy : ∀ m' : M₀, ((S₀.toCornerRing i₀ (tfull (.U q hq hqM)) • m' : M₀) : H1 (N * r) H₀ 𝒪) =
              heckeT (N * r) H₀ q 𝒪 (m' : H1 (N * r) H₀ 𝒪) := by
            intro m'
            rw [htc₀_smul, htfull _ hqN]
            rfl
          rw [htc_smul, hiα, hι, hEa _ hqN]
          have hval : heckeT (N * r * p) _ q 𝒪 (stab m) = stab (S₀.toCornerRing i₀ (tfull (.U q hq hqM)) • m) := by
            rw [hstab_def, hstab_def, map_sub, ← CohCarrier.iDeg_heckeT_comm_of_dvd h1 (Nat.coprime_one_right q) hqM,
              ← CohCarrier.iDeg_heckeT_comm_of_dvd hp' hcop hqM, ← hy m, ← hy (αt • m), hcommC₀]
          show S₁.e i₁ • heckeT (N * r * p) _ q 𝒪 (stab m) = _
          rw [hval]
          exact he_of_mem _ (hLc _)
        | dia d => exact absurd hg₀ id
      · refine ⟨1, fun m => ?_⟩
        rw [htc_smul, hiα, hι, hEc, hdiam_stab, one_smul]
        exact he_of_mem _ (hLc _)
    · rw [Set.mem_singleton_iff] at hxU
      subst hxU
      refine ⟨αt, fun m => ?_⟩
      rw [htc_smul, hiα, hU]
      have hval := PsiStubR.heckeT_stab_eq_stab_smul (𝒪 := 𝒪) (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)))
        h1 hp' S₀ i₀ tp αt hαt.2.1 htp.2.1 hdia σ hσ hUq m
      show S₁.e i₁ • heckeT (N * r * p) _ p 𝒪 (stab m) = _
      rw [show heckeT (N * r * p) _ p 𝒪 (stab m) = stab (αt • m) from hval]
      exact he_of_mem _ (hLc _)
  choose! yfun hyfun using hpartV

  have key := @AlgHom.exists_intertwiner_of_adjoin_eq_top_of_injective 𝒪 _ (S₁.CornerRing i₁) (S₀.CornerRing i₀) _ _ _ _
    M₁ M₀ _ _ _ _ _ _ _ _ iα hiα_inj hfaith₀ G hG yfun
  obtain ⟨res', hres', hres'G, hres'uniq⟩ := key (fun g hg m => Subtype.ext ((hyfun g hg m).trans (hiα _).symm))

  have hres'_char : ∀ (x : S₁.CornerRing i₁) (y₀ : S₀.CornerRing i₀),
      (∀ m : M₀, ((x • iα m : M₁) : V₁) = stab (y₀ • m)) → res' x = y₀ := by
    intro x y₀ hx
    have hzero : ∀ m : M₀, (res' x - y₀) • m = 0 := by
      intro m
      have h2 : iα (res' x • m) = iα (y₀ • m) := by
        rw [← hres' x m]
        exact Subtype.ext ((hx m).trans (hiα _).symm)
      have h3 := hiα_inj h2
      rw [sub_smul (res' x) y₀ m, h3, sub_self]
    exact sub_eq_zero.mp (hfaith₀ _ hzero)
  have hres'T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓNp : ¬ ℓ ∣ N * p) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓNr : ¬ ℓ ∣ N * r),
      res' (e₁.symm (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓNp hℓS))) =
        e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀
          (CuspForm.heckeAlgebra.T hℓ (fun h => hℓNp (h.trans (dvd_mul_right N p))) hℓS)) := by
    intro ℓ hℓ hℓNp hℓS hℓNr
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓN : ¬ ℓ ∣ N := fun h => hℓNp (h.trans (dvd_mul_right N p))
    have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hpS)
    have hℓNrp : ¬ ℓ ∣ N * r * p := by
      intro h
      rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
      · exact hℓNr h
      · exact hℓp ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h)
    have hcop : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ Fact.out).mpr hℓp
    apply hres'_char
    intro m
    rw [IdempotentSplitting.coe_cornerSmul, hiα]
    have hx := hTe₁ ℓ hℓ hℓNp hℓS hℓNrp (iα m)
    rw [IdempotentSplitting.coe_cornerSmul, hiα] at hx
    rw [hx, hstab_def, hstab_def, map_sub, ← CohCarrier.iDeg_heckeT_comm_of_coprime h1 (Nat.coprime_one_right ℓ) hℓ hℓNrp,
      ← CohCarrier.iDeg_heckeT_comm_of_coprime hp' hcop hℓ hℓNrp, ← hT₀ ℓ hℓ hℓN hℓS hℓNr m,
      ← hT₀ ℓ hℓ hℓN hℓS hℓNr (αt • m), hcommC₀]

  let S' : Finset ℕ := insert r S
  have hSS' : (↑S : Set ℕ) ⊆ (↑S' : Set ℕ) := by
    intro q hq; exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hq))
  let θ₁' : CuspForm.heckeAlgebra (N * p) 2 (↑S' : Set ℕ) →+* ResidueField 𝒪 :=
    θ₁.comp (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hSS')).toRingHom
  obtain ⟨Ψr, -, hΨr⟩ := CuspForm.heckeLocal.exists_algHom_of_subset (N * p) (↑S' : Set ℕ) (↑S : Set ℕ) hSS' 𝒪 θ₁ θ₁'
    (fun t => rfl)
  have hbij : Function.Bijective Ψr :=
    CuspForm.heckeLocal.bijective_of_subset_of_forall_prime_mem_of_charpoly_frobenius_eq p hp𝒪 ρbar habs S' S hpS
      (Finset.subset_insert r S) (N * p) hSNp θ₁ hθ₁ θ₁' (fun t => rfl) Ψr (fun t => hΨr t)
  let E : CuspForm.heckeLocal (N * p) (↑S' : Set ℕ) 𝒪 θ₁' ≃ₐ[𝒪] CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁ :=
    AlgEquiv.ofBijective Ψr hbij
  have hEapply : ∀ z, E z = Ψr z := fun z => rfl
  have hgen' : Algebra.adjoin 𝒪 (E.toAlgHom '' Set.range (CuspForm.heckeLocal.π (N * p) (↑S' : Set ℕ) 𝒪 θ₁')) = ⊤ := by
    rw [Algebra.adjoin_image, CuspForm.heckeLocal.adjoin_range_pi (N * p) (↑S' : Set ℕ) 𝒪 θ₁' Fact.out,
      Algebra.map_top, AlgHom.range_eq_top]
    exact E.surjective
  have hSNp' : ∀ q : ℕ, q.Prime → q ∣ N * p → q ∈ (↑S' : Set ℕ) := fun q hq h => hSS' (hSNp q hq h)
  have hF : res'.comp (e₁.symm : CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁ →ₐ[𝒪] S₁.CornerRing i₁) =
      res₁.comp (e₁.symm : CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁ →ₐ[𝒪] S₁.CornerRing i₁) := by
    apply AlgHom.ext_of_adjoin_eq_top hgen'
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    show res' (e₁.symm (E (CuspForm.heckeLocal.π (N * p) (↑S' : Set ℕ) 𝒪 θ₁' t))) =
      res₁ (e₁.symm (E (CuspForm.heckeLocal.π (N * p) (↑S' : Set ℕ) 𝒪 θ₁' t)))
    rw [hEapply, hΨr]

    have key := CuspForm.heckeAlgebra_ringHom_ext_of_primeFactors_subset (N := N * p) (S := (↑S' : Set ℕ)) hSNp'
      ((res'.comp (e₁.symm : _ →ₐ[𝒪] S₁.CornerRing i₁)).toRingHom.comp
        ((CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁).comp (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hSS')).toRingHom))
      ((res₁.comp (e₁.symm : _ →ₐ[𝒪] S₁.CornerRing i₁)).toRingHom.comp
        ((CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁).comp (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono hSS')).toRingHom))
      (by
        intro ℓ hℓ hℓNp hℓS'
        have hℓS : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS' (hSS' h)
        have hℓr : ℓ ≠ r := fun h => hℓS' (Finset.mem_coe.mpr (h ▸ Finset.mem_insert_self r S))
        have hℓNr : ¬ ℓ ∣ N * r := by
          intro h
          rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
          · exact hℓNp (h.mul_right p)
          · exact hℓr ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp h)
        have hincl : (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (N := N * p) (k := 2) hSS'))
              (CuspForm.heckeAlgebra.T hℓ hℓNp hℓS' : CuspForm.heckeAlgebra (N * p) 2 (↑S' : Set ℕ)) =
            (CuspForm.heckeAlgebra.T hℓ hℓNp hℓS : CuspForm.heckeAlgebra (N * p) 2 (↑S : Set ℕ)) := Subtype.ext rfl
        show res' (e₁.symm (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (Subalgebra.inclusion _ (CuspForm.heckeAlgebra.T hℓ hℓNp hℓS')))) =
          res₁ (e₁.symm (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (Subalgebra.inclusion _ (CuspForm.heckeAlgebra.T hℓ hℓNp hℓS'))))
        rw [hincl, hres'T ℓ hℓ hℓNp hℓS hℓNr, hconj3 ℓ hℓ hℓNp (fun h => hℓNp (h.trans (dvd_mul_right N p))) hℓS])
    exact RingHom.congr_fun key t
  have hreseq : res' = res₁ := by
    apply AlgHom.ext
    intro x
    have := AlgHom.congr_fun hF (e₁ x)
    simpa using this

  have hconj4 : res₁ (S₁.toCornerRing i₁ U) = αt := by
    rw [← hreseq]
    apply hres'_char
    intro m
    rw [show S₁.toCornerRing i₁ U = tc U from rfl, htc_smul, hiα, hU,
      PsiStubR.heckeT_stab_eq_stab_smul (𝒪 := 𝒪) (N * r) p H₀ (H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)))
        h1 hp' S₀ i₀ tp αt hαt.2.1 htp.2.1 hdia σ hσ hUq m]
    exact he_of_mem _ (hLc _)

  have hconj6 : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ N * r), q ∣ N →
      ∀ m : M₀, ((res₁ (S₁.toCornerRing i₁ (ι (tA (.U q hq hqM)))) • m : M₀) : H1 (N * r) H₀ 𝒪) =
        (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT (N * r) H₀ q 𝒪 (m : H1 (N * r) H₀ 𝒪)) := by
    intro q hq hqM hqN m
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have hqp : q ≠ p := fun h => hpN (h ▸ hqN)
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq Fact.out).mpr hqp
    have hy : ∀ m' : M₀, ((S₀.toCornerRing i₀ (tfull (.U q hq hqM)) • m' : M₀) : H1 (N * r) H₀ 𝒪) =
        heckeT (N * r) H₀ q 𝒪 (m' : H1 (N * r) H₀ 𝒪) := by
      intro m'
      rw [htc₀_smul, htfull _ hqN]
      rfl
    have hval : res₁ (S₁.toCornerRing i₁ (ι (tA (.U q hq hqM)))) = S₀.toCornerRing i₀ (tfull (.U q hq hqM)) := by
      rw [← hreseq]
      apply hres'_char
      intro m'
      rw [show S₁.toCornerRing i₁ (ι (tA (.U q hq hqM))) = tc (ι (tA (.U q hq hqM))) from rfl, htc_smul, hiα, hι, hEa _ hqN]
      have hval' : heckeT (N * r * p) _ q 𝒪 (stab m') = stab (S₀.toCornerRing i₀ (tfull (.U q hq hqM)) • m') := by
        rw [hstab_def, hstab_def, map_sub, ← CohCarrier.iDeg_heckeT_comm_of_dvd h1 (Nat.coprime_one_right q) hqM,
          ← CohCarrier.iDeg_heckeT_comm_of_dvd hp' hcop hqM, ← hy m', ← hy (αt • m'), hcommC₀]
      show S₁.e i₁ • heckeT (N * r * p) _ q 𝒪 (stab m') = _
      rw [hval']
      exact he_of_mem _ (hLc _)
    rw [hval, hy]

  have hle : Module.finrank 𝒪 ((Submodule.torsionBySet (S₁.CornerRing i₁) M₁ ↑(RingHom.ker (πT₁.comp e₁.toAlgHom))).restrictScalars 𝒪) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet (S₀.CornerRing i₀) M₀ ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))).restrictScalars 𝒪) :=
    CuspForm.heckeLocal.finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul p hp2 hp𝒪 ρbar habs hord S hS hpS N hpN hNS Smin hpSmin hSmin hmin hNmin hNunr htame
      r hr hr5 hrS hrN hr1 hrρ θ₁ hθ₁ θ₀ hθ₀ πT₀ πT₁ hπ H₀ hH₀ S₀ i₀ e₀ tp hT₀ htp hocc₀ hrk₀ hgen tfull htfull cfull hcfull
      hcofull hfaith₀ hdia αt hαt _ rfl ι hι U hU hgen₁ Sₐ iₐ S₁ i₁ e₁ h₁ₐ tA dA hE' h1 hp' hLa hLc
  have hge : Module.finrank 𝒪 ((Submodule.torsionBySet (S₀.CornerRing i₀) M₀ ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))).restrictScalars 𝒪) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet (S₁.CornerRing i₁) M₁ ↑(RingHom.ker (πT₁.comp e₁.toAlgHom))).restrictScalars 𝒪) := by
    let E₀ := (Submodule.torsionBySet (S₀.CornerRing i₀) M₀ ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))).restrictScalars 𝒪
    let E₁ := (Submodule.torsionBySet (S₁.CornerRing i₁) M₁ ↑(RingHom.ker (πT₁.comp e₁.toAlgHom))).restrictScalars 𝒪
    have hmap : ∀ m : M₀, m ∈ E₀ → iα m ∈ E₁ := by
      intro m hm
      rw [Submodule.restrictScalars_mem, Submodule.mem_torsionBySet_iff] at hm ⊢
      rintro ⟨t, ht⟩
      have ht' : t ∈ RingHom.ker (πT₁.comp e₁.toAlgHom) := ht
      have hrt : res₁ t ∈ RingHom.ker (πT₀.comp e₀.toAlgHom) := by
        have h1 : (πT₁.comp e₁.toAlgHom) t = 0 := ht'
        have h2 : ((πT₀.comp e₀.toAlgHom).comp res₁) t = 0 := by rw [← hconj2]; exact h1
        exact h2
      show t • iα m = 0
      rw [hres' t m, hreseq, hm ⟨res₁ t, hrt⟩, map_zero]
    let f : E₀ →ₗ[𝒪] E₁ := (iα.comp E₀.subtype).codRestrict E₁ (fun m => hmap m.1 m.2)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply hiα_inj
      exact congrArg Subtype.val hab
    exact LinearMap.finrank_le_finrank_of_injective hf
  exact ⟨res₁, hconj1, hconj2, hconj3, hconj4, le_antisymm hle hge, hconj6⟩

end S_CuspForm_heckeLocal_exists_algHom_cornerRing_levelLowering_unitRoot_of_degeneracy_level_mul
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_algHom_cornerRing_levelLowering_unitRoot_of_degeneracy_level_mul (solution)

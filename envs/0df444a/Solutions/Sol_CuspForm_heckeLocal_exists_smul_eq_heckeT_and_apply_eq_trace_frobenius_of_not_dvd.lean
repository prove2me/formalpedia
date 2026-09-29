-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b4587aa7-ae10-5bab-86c0-a4a8a4345fdf

import Mathlib
import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CuspForm_HeckeModuleCornerRealization
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Theorems.Thm_CuspForm_exists_heckeGaloisRepDatum_pi_eq_and_isUnramifiedAt_of_exists_galoisRep_of_point
import Theorems.Thm_CuspForm_exists_galoisRep_of_point
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Theorems.Thm_CuspForm_heckeLocal_adjoin_range_pi
import Theorems.Thm_CuspForm_heckeLocal_exists_point
import Theorems.Thm_CuspForm_heckeLocal_residue_surjective
import Theorems.Thm_GaloisRepAdic_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_GaloisRepAdic_charpoly_baseChangeAlong
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_CohCarrier_exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_CuspForm_isReduced_of_adjoin_range_heckeAlgebra_eq_top
import Theorems.Thm_IsDiscreteValuationRing_exists_algHom_pi_of_module_finite_free
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal AlgebraicClosure.Rat.isGalois FrobeniusDensity.liesOver_ratBelow Deformation.ProartinianCat.instCategory Deformation.ProartinianCat.topologicalSpace Deformation.ProartinianCat.instUniqueHomSelf Deformation.IsLocalProartinianAlgebra.toIsLocalHom Deformation.ProartinianCat.instDiscreteTopologyCarrierResidueField Deformation.ProartinianCat.algebra Deformation.IsLocalProartinianAlgebra.toIsLocalRing Deformation.IsLocalProartinianAlgebra.toIsProartinian Deformation.IsLocalProartinianAlgebra.toIsTopologicalRing Deformation.ProartinianCat.instCoeSortType Deformation.ProartinianCat.instUniqueHomResidueField Deformation.ProartinianCat.instIsLocalHomCarrierContinuousAlgHomHom Deformation.IsLocalProartinianAlgebra.toIsResidueAlgebra Deformation.ProartinianCat.isLocalProartinianAlgebra Deformation.ProartinianCat.instIsAdicTopologyCarrierSelf Deformation.ProartinianCat.commRing Deformation.ProartinianCat.instFieldCarrierResidueField IsLocalRing.instDiscreteTopologyQuotientIdealHPowNatMaximalIdeal_definitions IsLocalRing.instIsLinearTopology_definitions IsProartinian.toT0Space instIsProartinianOfDiscreteTopologyOfIsArtinianRing IsLocalRing.instIsAdicTopology instIsProartinianOfIsAdicTopologyOfIsNoetherianRingOfCompactSpace IsLocalRing.instIsHausdorffMaximalIdealOfIsNoetherianRing_definitions IsLocalRing.instNonarchimedeanRing_definitions IsLocalRing.instIsPrecompleteMaximalIdealOfCompactSpace_definitions IsLocalRing.instDiscreteTopologyOfIsArtinianRing_definitions IsLocalRing.instT2SpaceOfIsNoetherianRing_definitions IsProartinian.toCompleteSpace IsProartinian.toIsLinearTopology instTopologicallyFGOfFiniteType instMulSemiringActionSubtypeMemIntermediateFieldOfSMulCommClassOfNormal_definitions instIsLocalHomRingHomAlgebraMap_definitions instContinuousConstSMulConjActOfContinuousMul_definitions instIsLocalHomRingHomToRingHom_definitions_1 instIsLocalHomResidueFieldRingHomAlgebraMap_definitions instMulSemiringActionRingOfIntegers_definitions"
p2m_attr_erase "instance" "instIsLocalHomRingHomToRingHom_definitions instMulActionContinuousMonoidHomOfContinuousConstSMul_definitions instFiniteIndexMulOppositeOp_definitions ValuationSubring.smulCommClass instFaithfulSMulSubtypeMemValuationSubring_definitions ContinuousAlgHom.isLocalHom_id instIsModuleTopologyMatrixOfFiniteOfIsTopologicalRing_definitions IsTopologicalAddGroup.discreteUniformity IntermediateField.smulCommClass_of_normal instMulActionMonoidHomOfMulDistribMulAction_definitions IsTopologicalGroup.discreteUniformity instIsLocalHomRingHomOfContinuousAlgHom_definitions Additive.instDistrbMulAction instIsLocalHomRingHomOfContinuousAlgHom_definitions_1 instNumberFieldSubtypeMemIntermediateFieldOfFiniteDimensional_definitions ContinuousAlgHom.isLocalHom_comp instIsLocalHomContinuousAlgHomToContinuousAlgHom_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsResidueAlgebra.inst IsResidueAlgebra.instQuotientIdeal IsLocalRing.quot IsLocalHom.quotient_mk Deformation.ProartinianCat.ClosedSubalgebra.instNontrivialSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsLinearTopologySubtypeCarrierMemSubalgebra Deformation.ProartinianCat.ClosedSubalgebra.instIsTopologicalRingSubtypeCarrierMemSubalgebra Deformation.ProartinianCat.instFiniteResidueField Deformation.ProartinianCat.instCompactSpace TateModule.instModule TateModule.instSMul ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar"
p2m_attr_erase "instance" "ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec Deformation.ProartinianCat.Hom.mk.injEq Deformation.ProartinianCat.ofHom_comp Deformation.ProartinianCat.hom_comp Deformation.ProartinianCat.mk.sizeOf_spec Deformation.ProartinianCat.Hom.mk.sizeOf_spec Deformation.ProartinianCat.ofEquiv_hom_hom Deformation.ProartinianCat.ofHom_id Deformation.ProartinianCat.hom_id Deformation.ProartinianCat.ofEquiv_inv_hom Deformation.ProartinianCat.mk.injEq Deformation.ProartinianCat.ofHom_hom ContinuousMonoidHom.val_inv_toHomUnits_toFun Units.val_mapₜ_toFun MonoidHom.coe_smul ContinuousAlgHom.coe_toContinuousMonoidHom ContinuousMonoidHom.val_toHomUnits_toFun ContinuousMonoidHom.mk_toMonoidHom ContinuousAlgHom.mapMatrix_apply Units.val_inv_mapₜ_toFun Units.coeHomₜ_toFun ContinuousMonoidHom.coe_mk ContinuousMonoidHom.coe_smul AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom Deformation.repnFunctor_map Deformation.mapRepn_apply Deformation.ProartinianCat.closedSubalgebraι_apply Deformation.matrixRepresentation_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap HahnSeries.ramScale_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluPointMap2_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open Polynomial IsLocalRing CohCarrier IharaLemma ModularCurve.Period CuspForm
open scoped IsMulCommutative MatrixGroups

noncomputable section

namespace GalTqSol

section Generic

theorem trace_eq_neg_coeff_one {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ.trace σ = -(LinearMap.charpoly (ρ.ρ σ)).coeff 1 := by
  classical
  let b := Module.finBasisOfFinrankEq A ρ.V ρ.finrank_eq
  unfold GaloisRepAdic.trace
  rw [LinearMap.trace_eq_matrix_trace A b, ← LinearMap.charpoly_toMatrix (ρ.ρ σ) b,
    Matrix.trace_eq_neg_charpoly_coeff]
  simp

theorem coeff_one_quadratic {A : Type} [CommRing A] (x c : A) :
    (X ^ 2 - C x * X + C c : A[X]).coeff 1 = -x := by
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C]

theorem map_quadratic {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x c : A) :
    (X ^ 2 - C x * X + C c : A[X]).map f = X ^ 2 - C (f x) * X + C (f c) := by
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C]

theorem isLocalHom_of_finite {𝒪 T R : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T]
    [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
    (ψ : T →ₐ[𝒪] R) : IsLocalHom ψ.toRingHom := by
  let P : Ideal T := (maximalIdeal R).comap ψ.toRingHom
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hPO : P.comap (algebraMap 𝒪 T) = maximalIdeal 𝒪 := by
    refine ((maximalIdeal.isMaximal 𝒪).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    show ψ (algebraMap 𝒪 T a) ∈ maximalIdeal R
    rw [AlgHom.commutes]
    have hna : ¬ IsUnit a := (mem_maximalIdeal a).mp ha
    exact (mem_maximalIdeal _).mpr fun hu => hna ((isUnit_map_iff (algebraMap 𝒪 R) a).mp hu)
  have hPmax : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝒪) P (hPO ▸ maximalIdeal.isMaximal 𝒪)
  have hPeq : P = maximalIdeal T := IsLocalRing.eq_maximalIdeal hPmax
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  have hxP : x ∈ P := by rw [hPeq]; exact (mem_maximalIdeal x).mpr hxu
  have : ψ x ∈ maximalIdeal R := Ideal.mem_comap.mp hxP
  exact (mem_maximalIdeal _).mp this hx

theorem heckeAlgebra_induction (N' : ℕ) [NeZero N'] (S : Set ℕ)
    (hN'S : ∀ q : ℕ, q.Prime → q ∣ N' → q ∈ S)
    {R : Type} [Ring R] (F : heckeAlgebra N' 2 S →+* R) (B : Subring R)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S),
      F (heckeAlgebra.T hℓ hℓN' hℓS) ∈ B)
    (t : heckeAlgebra N' 2 S) : F t ∈ B := by
  classical
  obtain ⟨t, ht⟩ := t
  refine Algebra.adjoin_induction (p := fun t ht => F ⟨t, ht⟩ ∈ B) ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, hℓ, hℓN', hℓS, rfl⟩ | ⟨q, hqN', hq, hqS, rfl⟩)
    · exact hT ℓ hℓ hℓN' hℓS
    · exact absurd (hN'S q hq hqN') hqS
  · intro r
    have e : (⟨algebraMap ℤ _ r, algebraMap_mem _ r⟩ : heckeAlgebra N' 2 S) =
        (r : heckeAlgebra N' 2 S) := Subtype.ext (by simp)
    rw [e, map_intCast F r]
    exact intCast_mem _ r
  · intro x y hx hy hpx hpy
    have e : (⟨x + y, add_mem hx hy⟩ : heckeAlgebra N' 2 S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, RingHom.map_add]
    exact add_mem hpx hpy
  · intro x y hx hy hpx hpy
    have e : (⟨x * y, mul_mem hx hy⟩ : heckeAlgebra N' 2 S) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, RingHom.map_mul]
    exact mul_mem hpx hpy

end Generic

section Transport

variable (M : ℕ) (F : Type) [Field F]

abbrev PZ : Type := ↥(parabolicHoms ℤ (GammaH M ⊤) ℤ)
abbrev PF : Type := ↥(parabolicHoms F (GammaH M ⊤) F)

private def _root_.GalTqSol.ext : H1 M ⊤ ℤ →ₗ[ℤ] H1 M ⊤ F where
  toFun φ := (Int.castAddHom F).comp φ
  map_add' φ ψ := by ext; simp
  map_smul' n φ := by ext; simp

p2m_export "GalTqSol" "ext"
theorem ext_apply (φ : H1 M ⊤ ℤ) : ext M F φ = (Int.castAddHom F).comp φ := rfl

theorem ext_mem {φ : H1 M ⊤ ℤ} (hφ : φ ∈ parabolicHoms ℤ (GammaH M ⊤) ℤ) :
    ext M F φ ∈ parabolicHoms F (GammaH M ⊤) F := by
  rw [mem_parabolicHoms_iff] at hφ ⊢
  intro γ hγ
  rw [ext_apply, AddMonoidHom.comp_apply, hφ γ hγ, map_zero]

def extP : PZ M →ₗ[ℤ] PF M F where
  toFun φ := ⟨ext M F φ, ext_mem M F φ.2⟩
  map_add' φ ψ := Subtype.ext (by simp)
  map_smul' n φ := Subtype.ext (by simp)

theorem coe_extP (φ : PZ M) : (extP M F φ : H1 M ⊤ F) = (Int.castAddHom F).comp (φ : H1 M ⊤ ℤ) := rfl

theorem heckeT_ext (ℓ : ℕ) [NeZero ℓ] (φ : H1 M ⊤ ℤ) :
    heckeT M ⊤ ℓ F (ext M F φ) = ext M F (heckeT M ⊤ ℓ ℤ φ) :=
  heckeT_comp_coeff M ⊤ ℓ (Int.castAddHom F) φ

variable {M F}
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (PZ M)) (bF : Module.Basis (Fin n) F (PF M F))
  (hb : ∀ i, (bF i : H1 M ⊤ F) = (Int.castAddHom F).comp (b i : H1 M ⊤ ℤ))

include hb in
theorem extP_basis (i : Fin n) : extP M F (b i) = bF i := Subtype.ext (by rw [coe_extP, hb])

def ιF : Module.End ℤ (PZ M) →+* Module.End F (PF M F) :=
  ((Matrix.toLinAlgEquiv bF).toRingEquiv.toRingHom.comp (Int.castRingHom F).mapMatrix).comp
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom

theorem ιF_apply (f : Module.End ℤ (PZ M)) :
    ιF b bF f = Matrix.toLin bF bF ((LinearMap.toMatrix b b f).map (Int.castRingHom F)) := rfl

include hb in

theorem ιF_extP (f : Module.End ℤ (PZ M)) (φ : PZ M) :
    ιF b bF f (extP M F φ) = extP M F (f φ) := by
  classical
  suffices h : ((ιF b bF f).restrictScalars ℤ).comp (extP M F) = (extP M F).comp f from
    LinearMap.congr_fun h φ
  refine b.ext fun j => ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [extP_basis b bF hb j, ιF_apply, Matrix.toLin_self]
  conv_rhs => rw [← b.sum_repr (f (b j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, Int.coe_castRingHom, map_zsmul,
    extP_basis b bF hb i, Int.cast_smul_eq_zsmul]

end Transport

theorem exists_ringHom_parabolicHoms_field (M : ℕ) [NeZero M] (S : Set ℕ) (F : Type) [Field F]
    [CharZero F] :
    ∃ ρF : heckeAlgebra M 2 S →+* Module.End F (PF M F),
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ S) (ψ : PF M F),
        ((ρF (heckeAlgebra.T hℓ hℓM hℓS) ψ : PF M F) : H1 M ⊤ F) =
          (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M ⊤ ℓ F (ψ : H1 M ⊤ F)) := by
  classical
  haveI : (GammaH M ⊤).FiniteIndex := by rw [GammaH_top]; infer_instance
  obtain ⟨-, ρ, -, hρT, -⟩ := CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms M S
  obtain ⟨n, b, hbF⟩ := ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (GammaH M ⊤)
  obtain ⟨bF, hb⟩ := hbF F
  refine ⟨(ιF b bF).comp ρ, fun ℓ hℓ hℓM hℓS => ?_⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let Lm : PF M F →ₗ[F] H1 M ⊤ F :=
    (parabolicHoms F (GammaH M ⊤) F).subtype.comp ((ιF b bF).comp ρ (heckeAlgebra.T hℓ hℓM hℓS))
  let Rm : PF M F →ₗ[F] H1 M ⊤ F := (heckeTL M ⊤ F ℓ).comp (parabolicHoms F (GammaH M ⊤) F).subtype
  suffices h : Lm = Rm from fun ψ => LinearMap.congr_fun h ψ
  refine bF.ext fun j => ?_
  show (((ιF b bF).comp ρ (heckeAlgebra.T hℓ hℓM hℓS) (bF j) : PF M F) : H1 M ⊤ F) =
    heckeT M ⊤ ℓ F (bF j : H1 M ⊤ F)
  rw [RingHom.comp_apply, ← extP_basis b bF hb j, ιF_extP b bF hb, coe_extP, coe_extP,
    hρT ℓ hℓ hℓM hℓS (b j)]
  exact (heckeT_ext M F ℓ (b j : H1 M ⊤ ℤ)).symm

section Corner

variable {𝒪 : Type} [CommRing 𝒪]

theorem diamondL_top_eq_one (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : diamondL M ⊤ 𝒪 d = 1 := by
  apply LinearMap.ext
  intro φ
  show diamondRaw M ⊤ 𝒪 (Classical.choose (gamma0Units_surjective M d)) φ = φ
  set σ := Classical.choose (gamma0Units_surjective M d)
  have hσ : (σ : SL(2, ℤ)) ∈ GammaH M ⊤ := by rw [GammaH_top]; exact σ.2
  ext γ
  show φ (Additive.ofMul (conjHom M ⊤ σ (Additive.toMul γ))) = φ γ
  have hsplit : conjHom M ⊤ σ (Additive.toMul γ) =
      (⟨(σ : SL(2, ℤ)), hσ⟩ : ↥(GammaH M ⊤)) * Additive.toMul γ * (⟨(σ : SL(2, ℤ)), hσ⟩)⁻¹ := by
    apply Subtype.ext
    rfl
  rw [hsplit, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  simp only [ofMul_toMul]
  abel

theorem heckeTL_comm_of_primes (M : ℕ) (r ℓ : ℕ) (hr : r.Prime) (hℓ : ℓ.Prime) :
    (haveI : NeZero r := ⟨hr.ne_zero⟩; heckeTL M ⊤ 𝒪 r) *
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M ⊤ 𝒪 ℓ) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M ⊤ 𝒪 ℓ) *
        (haveI : NeZero r := ⟨hr.ne_zero⟩; heckeTL M ⊤ 𝒪 r) := by
  by_cases hrℓ : r = ℓ
  · subst hrℓ; rfl
  · haveI : NeZero r := ⟨hr.ne_zero⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    apply LinearMap.ext
    intro φ
    show heckeT M ⊤ r 𝒪 (heckeT M ⊤ ℓ 𝒪 φ) = heckeT M ⊤ ℓ 𝒪 (heckeT M ⊤ r 𝒪 φ)
    exact CohCarrier.heckeT_comm_of_prime M ⊤ r ℓ hr ((Nat.coprime_primes hr hℓ).mpr hrℓ) φ

theorem heckeTL_commute_opFamily (L : ℕ) [NeZero L] (S : Set ℕ) (r : ℕ) (hr : r.Prime)
    (g : Gen L S) :
    Commute (haveI : NeZero r := ⟨hr.ne_zero⟩; heckeTL L ⊤ 𝒪 r) (opFamily L ⊤ S 𝒪 g) := by
  cases g with
  | T ℓ hℓ hℓS hℓM => exact heckeTL_comm_of_primes L r ℓ hr hℓ
  | U ℓ hℓ hℓM => exact heckeTL_comm_of_primes L r ℓ hr hℓ
  | dia d =>
    show _ * diamondL L ⊤ 𝒪 d = diamondL L ⊤ 𝒪 d * _
    rw [diamondL_top_eq_one, mul_one, one_mul]

variable {k : Type} [Field k] [Algebra 𝒪 k]

theorem heckeTL_commute_of_mem (L : ℕ) [NeZero L] (S : Set ℕ)
    (hcomm : ∀ g h : Gen L S, opFamily L ⊤ S 𝒪 g * opFamily L ⊤ S 𝒪 h =
      opFamily L ⊤ S 𝒪 h * opFamily L ⊤ S 𝒪 g)
    (θbar : Gen L S → k) (r : ℕ) (hr : r.Prime)
    (b : ↥(hdata L ⊤ S 𝒪 k hcomm θbar).opSubalgebra) :
    Commute (haveI : NeZero r := ⟨hr.ne_zero⟩; heckeTL L ⊤ 𝒪 r) (b : Module.End 𝒪 (H1 L ⊤ 𝒪)) := by
  have hb : (b : Module.End 𝒪 (H1 L ⊤ 𝒪)) ∈ Algebra.adjoin 𝒪 (Set.range (opFamily L ⊤ S 𝒪)) := b.2
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
  rintro _ ⟨g, rfl⟩
  exact heckeTL_commute_opFamily L S r hr g

end Corner

section Torsion

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]

theorem isTorsionFree_H1 (L : ℕ) : Module.IsTorsionFree 𝒪 (H1 L ⊤ 𝒪) := by
  refine ⟨fun r hr φ ψ h => ?_⟩
  ext x
  have := congrArg (fun (χ : H1 L ⊤ 𝒪) => χ x) h
  simp only [AddMonoidHom.smul_apply, smul_eq_mul] at this
  exact hr.left this

theorem isTorsionFree_end {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.IsTorsionFree 𝒪 V] :
    Module.IsTorsionFree 𝒪 (Module.End 𝒪 V) := by
  refine ⟨fun r hr f g h => ?_⟩
  apply LinearMap.ext
  intro v
  have := LinearMap.congr_fun h v
  simp only [LinearMap.smul_apply] at this
  exact hr.isSMulRegular this

end Torsion

section Engine

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]

def stabSubring {V W : Type} [AddCommGroup V] [AddCommGroup W] {F : Type} [Field F] [Module F W]
    (ι : V →+ W) : Subring (Module.End F W) where
  carrier := {g | ∀ v : V, ∃ w : V, g (ι v) = ι w}
  mul_mem' := by
    intro g h hg hh v
    obtain ⟨w, hw⟩ := hh v
    obtain ⟨w', hw'⟩ := hg w
    exact ⟨w', by rw [Module.End.mul_apply, hw, hw']⟩
  one_mem' := fun v => ⟨v, rfl⟩
  add_mem' := by
    intro g h hg hh v
    obtain ⟨w, hw⟩ := hg v
    obtain ⟨w', hw'⟩ := hh v
    exact ⟨w + w', by rw [LinearMap.add_apply, hw, hw', map_add]⟩
  zero_mem' := fun v => ⟨0, by rw [LinearMap.zero_apply, map_zero]⟩
  neg_mem' := by
    intro g hg v
    obtain ⟨w, hw⟩ := hg v
    exact ⟨-w, by rw [LinearMap.neg_apply, hw, map_neg]⟩

theorem action
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (S : Finset ℕ) (hpS : p ∈ S) (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) [NeZero q]
    (N L : ℕ) [NeZero N] [NeZero L] (hqN : ¬ q ∣ N) (hLN : L ∣ N)
    (hNS : ∀ q' : ℕ, q'.Prime → q' ∣ N → q' ∈ S)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (ρT : GaloisRepAdic (heckeLocal N (↑S : Set ℕ) 𝒪 θ))
    (hρT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρT.ρ σ) =
            X ^ 2 - C (heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (heckeAlgebra.T hℓ hℓN hℓS)) * X +
              C (ℓ : heckeLocal N (↑S : Set ℕ) 𝒪 θ))
    (Pq : ValuationSubring (AlgebraicClosure ℚ)) (hPq : Pq.LiesOverPrime q)
    (σq : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσq : Pq.IsFrobeniusAt σq q)
    (V : Type) [AddCommGroup V] [Module 𝒪 V]
    (jK : V →ₗ[𝒪] H1 L ⊤ 𝒪) (hjK : Function.Injective jK)
    (hKpar : ∀ v : V, jK v ∈ parabolicHoms 𝒪 (GammaH L ⊤) 𝒪)
    (hK : ∀ (r : ℕ) (hr : r.Prime) (v : V), ∃ w : V,
      (haveI : NeZero r := ⟨hr.ne_zero⟩; heckeT L ⊤ r 𝒪 (jK v)) = jK w)
    (B : heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] Module.End 𝒪 V)
    (hB : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N) (v : V),
      jK (B (heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (heckeAlgebra.T hℓ hℓN hℓS)) v) =
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT L ⊤ ℓ 𝒪 (jK v))) :
    ∀ v : V, jK (B (ρT.trace σq) v) = heckeT L ⊤ q 𝒪 (jK v) := by
  classical
  have hint : CuspForm.HasIntegralStructure N 2 := Fact.out
  set T := heckeLocal N (↑S : Set ℕ) 𝒪 θ with hTdef
  set πN := heckeLocal.π N (↑S : Set ℕ) 𝒪 θ with hπNdef

  set S₁ : Finset ℕ := S.erase q with hS₁def
  have hqL : ¬ q ∣ L := fun h => hqN (h.trans hLN)
  have hLS₁ : ∀ r : ℕ, r.Prime → r ∣ L → r ∈ (↑S₁ : Set ℕ) := by
    intro r hr hrL
    refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨?_, hNS r hr (hrL.trans hLN)⟩)
    rintro rfl
    exact hqL hrL
  have hpS₁ : p ∈ S₁ := Finset.mem_erase.mpr ⟨hqp.symm, hpS⟩
  have hqS₁ : q ∉ (↑S₁ : Set ℕ) := fun h => by simp [hS₁def] at h
  have hS₁S : ∀ {ℓ : ℕ}, ℓ ∉ (↑S : Set ℕ) → ℓ ∉ (↑S₁ : Set ℕ) := fun h h' =>
    h (Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp h')))
  have hℓN_of : ∀ {ℓ : ℕ}, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N := fun hℓ hℓS h =>
    hℓS (Finset.mem_coe.mpr (hNS _ hℓ h))

  haveI : Module.Finite 𝒪 (H1 L ⊤ 𝒪) := CohCarrier.H1_moduleFinite L ⊤ 𝒪 𝒪
  haveI : IsNoetherian 𝒪 (H1 L ⊤ 𝒪) := isNoetherian_of_isNoetherianRing_of_finite 𝒪 _
  haveI : Module.Finite 𝒪 V := Module.Finite.of_injective jK hjK
  haveI := isTorsionFree_H1 (𝒪 := 𝒪) L
  haveI hKtf : Module.IsTorsionFree 𝒪 V :=
    Function.Injective.moduleIsTorsionFree jK hjK (fun c v => map_smul jK c v)
  haveI : Module.Free 𝒪 V := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite 𝒪 (Module.End 𝒪 V) := inferInstance
  haveI : IsNoetherian 𝒪 (Module.End 𝒪 V) :=
    isNoetherian_of_isNoetherianRing_of_finite 𝒪 (Module.End 𝒪 V)
  haveI hEtf : Module.IsTorsionFree 𝒪 (Module.End 𝒪 V) := isTorsionFree_end

  let F : Type := FractionRing 𝒪
  have hFinj : Function.Injective (algebraMap 𝒪 F) := IsFractionRing.injective 𝒪 F
  haveI : CharZero F := charZero_of_injective_algebraMap hFinj
  let extO : H1 L ⊤ 𝒪 →+ H1 L ⊤ F := AddMonoidHom.compHom (algebraMap 𝒪 F : 𝒪 →+* F).toAddMonoidHom
  have extO_apply : ∀ v : H1 L ⊤ 𝒪, extO v = (algebraMap 𝒪 F : 𝒪 →+* F).toAddMonoidHom.comp v :=
    fun v => rfl
  have extO_inj : Function.Injective extO := by
    intro v w h
    ext γ
    have := congrArg (fun χ : H1 L ⊤ F => χ γ) h
    exact hFinj this
  have extO_heckeT : ∀ (r : ℕ) [NeZero r] (v : H1 L ⊤ 𝒪),
      heckeT L ⊤ r F (extO v) = extO (heckeT L ⊤ r 𝒪 v) :=
    fun r _ v => heckeT_comp_coeff L ⊤ r (algebraMap 𝒪 F : 𝒪 →+* F).toAddMonoidHom v
  have extO_smul : ∀ (c : 𝒪) (v : H1 L ⊤ 𝒪), extO (c • v) = algebraMap 𝒪 F c • extO v := by
    intro c v
    ext γ
    simp [extO_apply, Algebra.smul_def]
  have extO_par : ∀ v : V, extO (jK v) ∈ parabolicHoms F (GammaH L ⊤) F := by
    intro v
    have hv := hKpar v
    rw [mem_parabolicHoms_iff] at hv ⊢
    intro γ hγ
    rw [extO_apply, AddMonoidHom.comp_apply, hv γ hγ, map_zero]
  let ιK : V →+ PF L F :=
    { toFun := fun v => ⟨extO (jK v), extO_par v⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun v w => Subtype.ext (by simp) }
  have ιK_coe : ∀ v : V, ((ιK v : PF L F) : H1 L ⊤ F) = extO (jK v) := fun v => rfl
  have ιK_inj : Function.Injective ιK := fun v w h =>
    hjK (extO_inj (congrArg Subtype.val h))
  have ιK_smul : ∀ (c : 𝒪) (v : V), ιK (c • v) = algebraMap 𝒪 F c • ιK v :=
    fun c v => Subtype.ext (by rw [ιK_coe, map_smul, extO_smul]; rfl)

  obtain ⟨ρF, hρF⟩ := exists_ringHom_parabolicHoms_field L (↑S₁ : Set ℕ) F

  have hstab : ∀ (x : heckeAlgebra L 2 (↑S₁ : Set ℕ)) (v : V), ∃ w : V, ρF x (ιK v) = ιK w := by
    intro x
    refine heckeAlgebra_induction L (↑S₁ : Set ℕ) hLS₁ ρF (stabSubring (F := F) ιK) ?_ x
    intro r hr hrL hrS₁ v
    haveI : NeZero r := ⟨hr.ne_zero⟩
    obtain ⟨w, hw⟩ := hK r hr v
    refine ⟨w, Subtype.ext ?_⟩
    rw [hρF r hr hrL hrS₁, ιK_coe, ιK_coe, extO_heckeT]
    exact congrArg extO hw

  choose πf hπf using hstab
  let πKlin : heckeAlgebra L 2 (↑S₁ : Set ℕ) → Module.End 𝒪 V := fun x =>
    { toFun := πf x
      map_add' := fun v w => ιK_inj (by
        rw [map_add, ← hπf, ← hπf, ← hπf, map_add, map_add])
      map_smul' := fun c v => ιK_inj (by
        rw [RingHom.id_apply, ιK_smul, ← hπf, ← hπf, ιK_smul, map_smul]) }
  have hπK : ∀ x v, ιK (πKlin x v) = ρF x (ιK v) := fun x v => (hπf x v).symm
  let πK : heckeAlgebra L 2 (↑S₁ : Set ℕ) →+* Module.End 𝒪 V :=
    { toFun := πKlin
      map_one' := LinearMap.ext fun v => ιK_inj (by rw [hπK, map_one]; rfl)
      map_mul' := fun x y => LinearMap.ext fun v => ιK_inj (by
        rw [hπK, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← hπK, ← hπK])
      map_zero' := LinearMap.ext fun v => ιK_inj (by rw [hπK, map_zero]; simp)
      map_add' := fun x y => LinearMap.ext fun v => ιK_inj (by
        rw [hπK, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hπK, hπK]) }
  have πK_apply : ∀ x v, ιK (πK x v) = ρF x (ιK v) := hπK

  have πK_T : ∀ (r : ℕ) (hr : r.Prime) (hrL : ¬ r ∣ L) (hrS₁ : r ∉ (↑S₁ : Set ℕ)) (v : V),
      jK (πK (heckeAlgebra.T hr hrL hrS₁) v) =
        (haveI : NeZero r := ⟨hr.ne_zero⟩; heckeT L ⊤ r 𝒪 (jK v)) := by
    intro r hr hrL hrS₁ v
    haveI : NeZero r := ⟨hr.ne_zero⟩
    apply extO_inj
    rw [← extO_heckeT, ← ιK_coe, ← ιK_coe, πK_apply, hρF r hr hrL hrS₁]

  let A : Subalgebra 𝒪 (Module.End 𝒪 V) := Algebra.adjoin 𝒪 (Set.range πK)
  have hAcomm : ∀ a ∈ Set.range πK, ∀ b ∈ Set.range πK, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  haveI : IsMulCommutative ↥A := Algebra.isMulCommutative_adjoin 𝒪 hAcomm
  haveI : Module.Finite 𝒪 ↥A := Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  haveI : Module.IsTorsionFree 𝒪 ↥A :=
    Function.Injective.moduleIsTorsionFree (fun x : ↥A => (x : Module.End 𝒪 V))
      Subtype.val_injective (fun _ _ => rfl)
  haveI : Module.Free 𝒪 ↥A := Module.free_of_finite_type_torsion_free' (R := 𝒪) (M := ↥A)
  have hπKA : ∀ x, πK x ∈ A := fun x => Algebra.subset_adjoin (Set.mem_range_self x)
  let πA : heckeAlgebra L 2 (↑S₁ : Set ℕ) →+* ↥A := πK.codRestrict A.toSubring hπKA
  have πA_coe : ∀ x, ((πA x : ↥A) : Module.End 𝒪 V) = πK x := fun x => rfl
  have hadjA : Algebra.adjoin 𝒪 (Set.range πA) = ⊤ := by
    apply Subalgebra.map_injective (f := A.val) Subtype.val_injective
    rw [Algebra.map_top, Subalgebra.range_val, ← Algebra.adjoin_image]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨πA x, ⟨x, rfl⟩, rfl⟩
  haveI : IsReduced ↥A :=
    CuspForm.isReduced_of_adjoin_range_heckeAlgebra_eq_top (N := L) (S := (↑S₁ : Set ℕ)) hLS₁ πA hadjA

  obtain ⟨n, R, _, _, _, _, _, _, _, _, ιA, hιA⟩ :=
    IsDiscreteValuationRing.exists_algHom_pi_of_module_finite_free (𝒪 := 𝒪) ↥A

  have hBπ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
      B (πN (heckeAlgebra.T hℓ hℓN hℓS)) =
        πK (heckeAlgebra.T hℓ (fun h => hℓN (h.trans hLN)) (hS₁S hℓS)) := by
    intro ℓ hℓ hℓS hℓN
    apply LinearMap.ext
    intro v
    apply hjK
    rw [hB ℓ hℓ hℓS hℓN v, πK_T]
  have hBA : ∀ t : T, B t ∈ A := by
    have hgen : ∀ x : heckeAlgebra N 2 (↑S : Set ℕ), B (πN x) ∈ A := by
      intro x
      refine heckeAlgebra_induction N (↑S : Set ℕ) (fun r hr hrN => Finset.mem_coe.mpr (hNS r hr hrN))
        ((B : T →+* Module.End 𝒪 V).comp πN) A.toSubring ?_ x
      intro ℓ hℓ hℓN hℓS
      show B (πN (heckeAlgebra.T hℓ hℓN hℓS)) ∈ A
      rw [hBπ ℓ hℓ hℓS hℓN]
      exact hπKA _
    have htop : (⊤ : Subalgebra 𝒪 T) ≤ A.comap B := by
      rw [← CuspForm.heckeLocal.adjoin_range_pi N (↑S : Set ℕ) 𝒪 θ hint]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      exact hgen x
    intro t
    exact htop (Algebra.mem_top : t ∈ (⊤ : Subalgebra 𝒪 T))
  let BA : T →ₐ[𝒪] ↥A := B.codRestrict A hBA
  have BA_coe : ∀ t, ((BA t : ↥A) : Module.End 𝒪 V) = B t := fun t => rfl
  have hBAπ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
      BA (πN (heckeAlgebra.T hℓ hℓN hℓS)) =
        πA (heckeAlgebra.T hℓ (fun h => hℓN (h.trans hLN)) (hS₁S hℓS)) :=
    fun ℓ hℓ hℓS hℓN => Subtype.ext (hBπ ℓ hℓ hℓS hℓN)

  set t : T := ρT.trace σq with htdef
  have hcoord : ∀ j : Fin n, ιA (BA t) j = ιA (πA (heckeAlgebra.T hq hqL hqS₁)) j := by
    intro j

    let ψ : T →ₐ[𝒪] R j := (Pi.evalAlgHom 𝒪 R j).comp (ιA.comp BA)
    let χ : heckeAlgebra L 2 (↑S₁ : Set ℕ) →+* R j :=
      ((Pi.evalRingHom R j).comp (ιA : ↥A →+* ∀ j, R j)).comp πA
    have hψχ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N),
        ψ (πN (heckeAlgebra.T hℓ hℓN hℓS)) =
          χ (heckeAlgebra.T hℓ (fun h => hℓN (h.trans hLN)) (hS₁S hℓS)) := by
      intro ℓ hℓ hℓS hℓN
      show ιA (BA (πN (heckeAlgebra.T hℓ hℓN hℓS))) j = ιA (πA _) j
      rw [hBAπ ℓ hℓ hℓS hℓN]

    have hpR : (p : R j) ∈ maximalIdeal (R j) := by
      have h := (mem_maximalIdeal _).mp hp𝒪
      rw [← map_natCast (algebraMap 𝒪 (R j)) p]
      exact (mem_maximalIdeal _).mpr fun hu => h ((isUnit_map_iff (algebraMap 𝒪 (R j)) _).mp hu)

    obtain ⟨𝒪'', _, _, _, _, _, _, _, _, _, hinj, ρj, hρj, -⟩ :=
      CuspForm.exists_galoisRep_of_point p L S₁ hpS₁
        (fun r hr hrL => Finset.mem_coe.mp (hLS₁ r hr hrL)) (R j) hpR χ

    haveI hψloc : IsLocalHom ψ.toRingHom := isLocalHom_of_finite ψ
    let φ : T →+* 𝒪'' := (algebraMap (R j) 𝒪'').comp ψ.toRingHom
    haveI hφ : IsLocalHom φ := RingHom.isLocalHom_comp _ _
    set bc : GaloisRepAdic 𝒪'' := ρT.baseChangeAlong φ hφ with hbcdef
    have hall : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        LinearMap.charpoly (bc.ρ σ) = LinearMap.charpoly (ρj.ρ σ) := by
      refine GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq bc ρj S ?_
      intro ℓ hℓ hℓS P τ hP hτ
      have hℓS' : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS (Finset.mem_coe.mp h)
      have hℓN : ¬ ℓ ∣ N := hℓN_of hℓ hℓS'
      have hℓL : ¬ ℓ ∣ L := fun h => hℓN (h.trans hLN)
      have hφT : φ (πN (heckeAlgebra.T hℓ hℓN hℓS')) =
          algebraMap (R j) 𝒪'' (χ (heckeAlgebra.T hℓ hℓL (hS₁S hℓS'))) := by
        show algebraMap (R j) 𝒪'' (ψ (πN (heckeAlgebra.T hℓ hℓN hℓS'))) = _
        rw [hψχ ℓ hℓ hℓS' hℓN]
      rw [hbcdef, GaloisRepAdic.charpoly_baseChangeAlong, hρT ℓ hℓ hℓN hℓS' P hP τ hτ,
        hρj ℓ hℓ hℓL (hS₁S hℓS') P hP τ hτ, map_quadratic, map_natCast, hφT]

    have hq' := hall σq
    rw [hbcdef, GaloisRepAdic.charpoly_baseChangeAlong, hρj q hq hqL hqS₁ Pq hPq σq hσq] at hq'
    have hc := congrArg (fun P : 𝒪''[X] => P.coeff 1) hq'
    simp only [Polynomial.coeff_map, coeff_one_quadratic] at hc
    have ht' : φ t = algebraMap (R j) 𝒪'' (χ (heckeAlgebra.T hq hqL hqS₁)) := by
      rw [htdef, trace_eq_neg_coeff_one, map_neg, hc, neg_neg]
    exact hinj ht'
  have hBt : B t = πK (heckeAlgebra.T hq hqL hqS₁) := by
    have h1 : ιA (BA t) = ιA (πA (heckeAlgebra.T hq hqL hqS₁)) := funext hcoord
    have h2 : BA t = πA (heckeAlgebra.T hq hqL hqS₁) := hιA h1
    have h3 := congrArg (fun x : ↥A => (x : Module.End 𝒪 V)) h2
    exact h3
  intro v
  rw [hBt, πK_T q hq hqL hqS₁ v]

theorem value
    (S : Finset ℕ) (q : ℕ) (N : ℕ) [NeZero N]
    (hNS : ∀ q' : ℕ, q'.Prime → q' ∣ N → q' ∈ S)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (πT : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] 𝒪)
    (a : 𝒪)
    (ha : ∃ ρ' : GaloisRepAdic 𝒪,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ'.ρ σ) =
              X ^ 2 - C (πT (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ
                (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) * X + C (ℓ : 𝒪)) ∧
      ρ'.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
          LinearMap.trace 𝒪 _ (ρ'.ρ σ) = a)
    (ρT : GaloisRepAdic (heckeLocal N (↑S : Set ℕ) 𝒪 θ))
    (hρT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρT.ρ σ) =
            X ^ 2 - C (heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (heckeAlgebra.T hℓ hℓN hℓS)) * X +
              C (ℓ : heckeLocal N (↑S : Set ℕ) 𝒪 θ))
    (Pq : ValuationSubring (AlgebraicClosure ℚ)) (hPq : Pq.LiesOverPrime q)
    (σq : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσq : Pq.IsFrobeniusAt σq q) :
    πT (ρT.trace σq) = a := by
  classical
  obtain ⟨ρ', hρ', -, hρ'q⟩ := ha
  haveI hloc : IsLocalHom πT.toRingHom := isLocalHom_of_finite πT
  set bc : GaloisRepAdic 𝒪 := ρT.baseChangeAlong πT.toRingHom hloc with hbcdef
  have hall : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (bc.ρ σ) = LinearMap.charpoly (ρ'.ρ σ) := by
    refine GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq bc ρ' S ?_
    intro ℓ hℓ hℓS P τ hP hτ
    have hℓS' : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS (Finset.mem_coe.mp h)
    have hℓN : ¬ ℓ ∣ N := fun h => hℓS (hNS ℓ hℓ h)
    rw [hbcdef, GaloisRepAdic.charpoly_baseChangeAlong, hρT ℓ hℓ hℓN hℓS' P hP τ hτ,
      hρ' ℓ hℓ hℓN hℓS' P hP τ hτ, map_quadratic, map_natCast]
    rfl
  have hq' := hall σq
  rw [hbcdef, GaloisRepAdic.charpoly_baseChangeAlong] at hq'
  have htr : ρ'.trace σq = a := hρ'q Pq hPq σq hσq
  rw [trace_eq_neg_coeff_one, ← hq', Polynomial.coeff_map] at htr
  rw [trace_eq_neg_coeff_one, map_neg]
  exact htr

end Engine

end GalTqSol

end

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
open GalTqSol in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hqS : q ∈ S) [NeZero q]
    (N L : ℕ) [NeZero N] [NeZero L] (hqN : ¬ q ∣ N) (hLN : L ∣ N)
    (hNS : ∀ q' : ℕ, q'.Prime → q' ∣ N → q' ∈ S)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (πT : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ →ₐ[𝒪] 𝒪)
    (a : 𝒪)
    (ha : ∃ ρ' : GaloisRepAdic 𝒪,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            LinearMap.charpoly (ρ'.ρ σ) =
              X ^ 2 - C (πT (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ
                (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) * X + C (ℓ : 𝒪)) ∧
      ρ'.IsUnramifiedAt q ∧
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ q →
          LinearMap.trace 𝒪 _ (ρ'.ρ σ) = a)

    (M : Type) [AddCommGroup M] [Module (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M] [Module 𝒪 M]
    [IsScalarTower 𝒪 (CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ) M]
    (hcomm : ∀ g h : CohCarrier.Gen L (↑S : Set ℕ),
      CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen L (↑S : Set ℕ) → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata L ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen L (↑S : Set ℕ), πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata L ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N),
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓL) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    (hpar : ∀ v : CohCarrier.H1 L ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH L ⊤) 𝒪)
    (e : M ≃ₗ[𝒪] ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀)))
    (hequiv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N) (m : M),
      ((e (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) • m) :
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀))) : CohCarrier.H1 L ⊤ 𝒪) =
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          CohCarrier.heckeT L ⊤ ℓ 𝒪
            ((e m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀))) :
              CohCarrier.H1 L ⊤ 𝒪))) :
    ∃ t : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ,
      (∀ m : M,
        ((e (t • m) : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀))) :
            CohCarrier.H1 L ⊤ 𝒪) =
          CohCarrier.heckeT L ⊤ q 𝒪
            ((e m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀))) :
              CohCarrier.H1 L ⊤ 𝒪)) ∧
      πT t = a := by
  classical
  have hint : CuspForm.HasIntegralStructure N 2 := Fact.out
  set T := CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ with hTdef
  set πN := CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ with hπNdef

  obtain ⟨H, hHπ, -⟩ :=
    CuspForm.exists_heckeGaloisRepDatum_pi_eq_and_isUnramifiedAt_of_exists_galoisRep_of_point
      CuspForm.exists_galoisRep_of_point p N S hpS hNS hp𝒪 θ ρbar habs hθ
      T πN
      (CuspForm.heckeLocal.residue_pi N (↑S : Set ℕ) 𝒪 θ)
      (CuspForm.heckeLocal.adjoin_range_pi N (↑S : Set ℕ) 𝒪 θ hint)
      (CuspForm.heckeLocal.exists_point N (↑S : Set ℕ) 𝒪 θ hint)
      (CuspForm.heckeLocal.residue_surjective N (↑S : Set ℕ) 𝒪 θ)
  have hρT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (H.ρ.ρ σ) =
            X ^ 2 - C (πN (heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : T) := by
    intro ℓ hℓ hℓN hℓS P hP σ hσ
    rw [H.charpoly_frob ℓ hℓ hℓN hℓS P hP σ hσ, hHπ]

  obtain ⟨Pq, hPq, σq, hσq⟩ := ValuationSubring.exists_isFrobeniusAt_rat q hq
  refine ⟨H.ρ.trace σq, ?_, value S q N hNS θ πT a ha H.ρ hρT Pq hPq σq hσq⟩

  set E : Module.End 𝒪 (H1 L ⊤ 𝒪) :=
    ((Sp.e i₀ : ↥(CohCarrier.hdata L ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra) :
      Module.End 𝒪 (H1 L ⊤ 𝒪)) with hEdef
  let jK : M →ₗ[𝒪] H1 L ⊤ 𝒪 :=
    { toFun := fun m =>
        ((e m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀))) : H1 L ⊤ 𝒪)
      map_add' := fun m m' => by rw [map_add]; rfl
      map_smul' := fun c m => by rw [LinearEquiv.map_smul]; rfl }
  have jK_apply : ∀ m : M, jK m =
      ((e m : ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀))) : H1 L ⊤ 𝒪) :=
    fun m => rfl
  have hjK : Function.Injective jK := fun m m' h =>
    e.injective (Subtype.ext (by rw [← jK_apply, ← jK_apply, h]))
  have hKpar : ∀ m : M, jK m ∈ parabolicHoms 𝒪 (GammaH L ⊤) 𝒪 := fun m => hpar _ (e m).2
  have hK : ∀ (r : ℕ) (hr : r.Prime) (m : M), ∃ m' : M,
      (haveI : NeZero r := ⟨hr.ne_zero⟩; heckeT L ⊤ r 𝒪 (jK m)) = jK m' := by
    intro r hr m
    haveI : NeZero r := ⟨hr.ne_zero⟩
    have hc := heckeTL_commute_of_mem (𝒪 := 𝒪) L (↑S : Set ℕ) hcomm θbar r hr (Sp.e i₀)

    have hfix : E (jK m) = jK m := Sp.e_smul_coe i₀ (e m)
    have hmem : heckeTL L ⊤ 𝒪 r (jK m) ∈
        IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) := by
      refine ⟨heckeTL L ⊤ 𝒪 r (jK m), ?_⟩
      show E (heckeTL L ⊤ 𝒪 r (jK m)) = heckeTL L ⊤ 𝒪 r (jK m)
      have := LinearMap.congr_fun hc.eq (jK m)
      simp only [Module.End.mul_apply] at this
      rw [← hEdef] at this
      rw [← this, hfix]
    refine ⟨e.symm ⟨heckeTL L ⊤ 𝒪 r (jK m), hmem⟩, ?_⟩
    show heckeTL L ⊤ 𝒪 r (jK m) =
      ((e (e.symm ⟨heckeTL L ⊤ 𝒪 r (jK m), hmem⟩) :
        ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀))) : H1 L ⊤ 𝒪)
    rw [LinearEquiv.apply_symm_apply]
  let B : T →ₐ[𝒪] Module.End 𝒪 M := Algebra.lsmul 𝒪 𝒪 M
  have B_apply : ∀ (t : T) (m : M), B t m = t • m := fun t m => rfl
  have hB : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ N) (m : M),
      jK (B (πN (heckeAlgebra.T hℓ hℓN hℓS)) m) =
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT L ⊤ ℓ 𝒪 (jK m)) := by
    intro ℓ hℓ hℓS hℓN m
    rw [B_apply, jK_apply, jK_apply]
    exact hequiv ℓ hℓ hℓS hℓN m

  have hact := action p hp𝒪 S hpS q hq hqp N L hqN hLN hNS θ H.ρ hρT Pq hPq σq hσq M jK hjK
    hKpar hK B hB
  intro m
  have h := hact m
  rw [B_apply, jK_apply, jK_apply] at h
  exact h

end S_CuspForm_heckeLocal_exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd (solution)

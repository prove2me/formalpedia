-- Prove2me | solution 1 for CohCarrier.eq_zero_of_mem_parabolicHoms_of_jDeg_eq_zero_of_apply_T_sq_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2a192275-c4bd-5087-a67a-9ea4ddeba490

import Theorems.Thm_CohCarrier_heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero
import Theorems.Thm_CohCarrier_exists_ringHom_heckeAlgebra_and_forall_exists_eigenclass_of_ker_eq
import Theorems.Thm_CuspForm_sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform
import Theorems.Thm_CuspForm_exists_isNewform_point_factor
import Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_top
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CohCarrier_exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Definitions.Def_CohCarrier_Inst
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_eq_zero_of_mem_parabolicHoms_of_jDeg_eq_zero_of_apply_T_sq_ne
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero"
p2m_attr_erase "simp" "ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open CohCarrier ModularCurve.Period CuspForm

namespace ROldSol

theorem heckeT_mem_parabolicHoms (M : ℕ) [NeZero M] (K : Type) [Field K] [CharZero K]
    (ℓ : ℕ) [NeZero ℓ] (φ : H1 M ⊤ K) (hφ : φ ∈ parabolicHoms K (GammaH M ⊤) K) :
    heckeT M ⊤ ℓ K φ ∈ parabolicHoms K (GammaH M ⊤) K := by
  classical
  haveI : (GammaH M ⊤).FiniteIndex := by rw [GammaH_top]; infer_instance
  obtain ⟨hZ, -⟩ := CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms M (∅ : Set ℕ)
  obtain ⟨n, b, hbF⟩ := ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (GammaH M ⊤)
  obtain ⟨bK, hb⟩ := hbF K

  set φ' : ↥(parabolicHoms K (GammaH M ⊤) K) := ⟨φ, hφ⟩ with hφ'def
  have hφsum : φ = ∑ i, (bK.repr φ' i) • (bK i : H1 M ⊤ K) := by
    have h := (bK.sum_repr φ').symm
    have h' := congrArg Subtype.val h
    rw [hφ'def] at h'
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    exact h'
  rw [hφsum, ← heckeTL_apply, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [heckeTL_apply, hb i, heckeT_comp_coeff M ⊤ ℓ (Int.castAddHom K) (b i : H1 M ⊤ ℤ)]

  have hmem := hZ ℓ (b i : H1 M ⊤ ℤ) (b i).2
  rw [mem_parabolicHoms_iff] at hmem ⊢
  intro γ hγ
  rw [AddMonoidHom.comp_apply, hmem γ hγ, map_zero]

theorem heckeAlgebra_induction' (N' : ℕ) [NeZero N'] (S : Set ℕ)
    {R : Type} [Ring R] (F : heckeAlgebra N' 2 S →+* R) (B : Subring R)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S),
      F (heckeAlgebra.T hℓ hℓN' hℓS) ∈ B)
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN' : q ∣ N') (hqS : q ∉ S),
      F (heckeAlgebra.U hq hqN' hqS) ∈ B)
    (t : heckeAlgebra N' 2 S) : F t ∈ B := by
  classical
  obtain ⟨t, ht⟩ := t
  refine Algebra.adjoin_induction (p := fun t ht => F ⟨t, ht⟩ ∈ B) ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, hℓ, hℓN', hℓS, rfl⟩ | ⟨q, hqN', hq, hqS, rfl⟩)
    · exact hT ℓ hℓ hℓN' hℓS
    · exact hU q hq hqN' hqS
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

theorem injective_of_isIntegral_int {A B : Type} [CommRing A] [IsDomain A] [Algebra.IsIntegral ℤ A]
    [Ring B] [CharZero B] [Nontrivial B] (f : A →+* B) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [eq_bot_iff]
  intro z hz
  rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast] at hz
  rw [Ideal.mem_bot]
  exact_mod_cast hz

end ROldSol

end

open ROldSol CohCarrier ModularCurve.Period CuspForm ModularFormClass in
theorem solution
    (F : Type) [Field F] [CharZero F]
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (r : ℕ) [NeZero r] (hr : r.Prime) (hrS : r ∉ (↑S : Set ℕ)) (hrN : ¬ r ∣ N)

    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* F)
    (hχr : χ (CuspForm.heckeAlgebra.T hr hrN hrS) ^ 2 ≠ ((r : F) + 1) ^ 2)
    (hχE : ∃ (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀N : ¬ ℓ₀ ∣ N) (hℓ₀S : ℓ₀ ∉ (↑S : Set ℕ)),
      ℓ₀ ≠ r ∧ χ (CuspForm.heckeAlgebra.T hℓ₀ hℓ₀N hℓ₀S) ≠ (ℓ₀ : F) + 1)

    (h₁ : CohCarrier.LevelLE N (N * r) ⊤ ⊤ 1) (hr' : CohCarrier.LevelLE N (N * r) ⊤ ⊤ r)

    (c : CohCarrier.H1 (N * r) ⊤ F)
    (hc : c ∈ ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH (N * r) ⊤) F)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), ℓ ≠ r →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT (N * r) ⊤ ℓ F c) =
        χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) • c)

    (hc₁ : CohCarrier.jDeg N (N * r) ⊤ ⊤ 1 F h₁ c = 0)
    (hcr : CohCarrier.jDeg N (N * r) ⊤ ⊤ r F hr' c = 0) :
    c = 0 := by
  classical
  haveI hNr : NeZero (N * r) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne r)⟩

  set U : Module.End F (H1 (N * r) ⊤ F) := heckeTL (N * r) ⊤ F r with hUdef
  have hUapply : ∀ φ : H1 (N * r) ⊤ F, U φ = heckeT (N * r) ⊤ r F φ := fun φ => rfl

  have hUU : U (U c) = c := by
    rw [hUapply, hUapply]
    exact CohCarrier.heckeT_heckeT_eq_self_of_jDeg_one_eq_zero_of_jDeg_eq_zero N r hr hrN F h₁ hr' c hc₁ hcr

  have main : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → c + (ε : F) • U c = 0 := by
    intro ε hε
    have hεF : (ε : F) * (ε : F) = 1 := by
      rcases hε with rfl | rfl <;> push_cast <;> norm_num
    by_contra hne
    set cε : H1 (N * r) ⊤ F := c + (ε : F) • U c with hcεdef

    have hUε : U cε = (ε : F) • cε := by
      rw [hcεdef, map_add, map_smul, hUU, smul_add, smul_smul, hεF, one_smul, add_comm]

    have hcεpar : cε ∈ parabolicHoms F (GammaH (N * r) ⊤) F := by
      refine add_mem hc (Submodule.smul_mem _ _ ?_)
      rw [hUapply]
      exact heckeT_mem_parabolicHoms (N * r) F r c hc

    have hTε : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), ℓ ≠ r →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT (N * r) ⊤ ℓ F cε) =
          χ (heckeAlgebra.T hℓ hℓN hℓS) • cε := by
      intro ℓ hℓ hℓN hℓS hℓr
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      have hcomm : heckeT (N * r) ⊤ ℓ F (U c) = U (heckeT (N * r) ⊤ ℓ F c) := by
        rw [hUapply, hUapply]
        exact CohCarrier.heckeT_comm_of_prime (N * r) ⊤ ℓ r hℓ ((Nat.coprime_primes hℓ hr).mpr hℓr) c
      rw [hcεdef, ← heckeTL_apply, map_add, map_smul, heckeTL_apply, heckeTL_apply, hcomm,
        heig ℓ hℓ hℓN hℓS hℓr, map_smul, smul_add, smul_comm]

    set aF : ℕ → F := fun m => if m = r then (ε : F) else
      if h : m.Prime ∧ ¬ m ∣ N ∧ m ∉ (↑S : Set ℕ) then χ (heckeAlgebra.T h.1 h.2.1 h.2.2) else 0
      with haFdef
    have haF_r : aF r = (ε : F) := by rw [haFdef]; simp
    have haF_of_ne : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), ℓ ≠ r →
        aF ℓ = χ (heckeAlgebra.T hℓ hℓN hℓS) := by
      intro ℓ hℓ hℓN hℓS hℓr
      rw [haFdef]
      simp only [hℓr, if_false]
      rw [dif_pos ⟨hℓ, hℓN, hℓS⟩]
    have heigε : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ (↑S : Set ℕ) →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT (N * r) ⊤ ℓ F cε) = aF ℓ • cε := by
      intro ℓ hℓ hℓS
      by_cases hℓr : ℓ = r
      · subst hℓr
        rw [haF_r, ← hUε, hUapply]
      · have hℓN : ¬ ℓ ∣ N := fun h => hℓS (Finset.mem_coe.mpr (hNS ℓ hℓ h))
        rw [haF_of_ne ℓ hℓ hℓN hℓS hℓr]
        exact hTε ℓ hℓ hℓN hℓS hℓr

    obtain ⟨χε, hχεT, hχεU, hdesc⟩ :=
      CohCarrier.exists_ringHom_heckeAlgebra_and_forall_exists_eigenclass_of_ker_eq
        (N * r) (↑S : Set ℕ) F cε hcεpar hne aF heigε

    obtain ⟨M₀, instM₀, hM₀N, g₀, hg₀, chig₀, hchig₀, iota₀, hiota₀⟩ :=
      CuspForm.exists_isNewform_point_factor N S hNS F χ
    have hrM₀ : ¬ r ∣ M₀ := fun h => hrN (h.trans hM₀N)

    haveI : Module.Finite ℤ (heckeAlgebra M₀ 2 (↑S : Set ℕ)) := CuspForm.moduleFinite_heckeAlgebra_two M₀ _
    haveI : Algebra.IsIntegral ℤ (heckeAlgebra M₀ 2 (↑S : Set ℕ)) := Algebra.IsIntegral.of_finite ℤ _
    haveI hRgint : Algebra.IsIntegral ℤ chig₀.range := by
      refine ⟨fun y => ?_⟩
      obtain ⟨y, t, rfl⟩ := y
      have ht : IsIntegral ℤ (chig₀ t) :=
        (Algebra.IsIntegral.isIntegral (R := ℤ) t).map chig₀.toIntAlgHom
      exact (isIntegral_algHom_iff (chig₀.range.subtype.toIntAlgHom) Subtype.val_injective).mp ht
    have hiota_inj : Function.Injective iota₀ := injective_of_isIntegral_int iota₀

    have hrange : ∀ t, χε t ∈ iota₀.range := by
      refine heckeAlgebra_induction' (N * r) (↑S : Set ℕ) χε iota₀.range ?_ ?_
      · intro ℓ hℓ hℓL hℓS
        have hℓN : ¬ ℓ ∣ N := fun h => hℓL (h.mul_right r)
        have hℓr : ℓ ≠ r := fun h => hℓL (h ▸ dvd_mul_left r N)
        rw [hχεT ℓ hℓ hℓL hℓS, haF_of_ne ℓ hℓ hℓN hℓS hℓr, ← hiota₀ ℓ hℓ hℓN hℓS]
        exact ⟨_, rfl⟩
      · intro q hq hqL hqS
        have hqr : q = r := by
          rcases (Nat.Prime.dvd_mul hq).mp hqL with h | h
          · exact absurd (Finset.mem_coe.mpr (hNS q hq h)) hqS
          · exact (Nat.prime_dvd_prime_iff_eq hq hr).mp h
        subst hqr
        rw [hχεU q hq hqL hqS, haF_r]
        exact ⟨(ε : chig₀.range), by rw [map_intCast]⟩

    set e : chig₀.range ≃+* iota₀.range := RingEquiv.ofBijective iota₀.rangeRestrict
      ⟨fun x y hxy => hiota_inj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective iota₀⟩
      with hedef
    set ψ₀ : heckeAlgebra (N * r) 2 (↑S : Set ℕ) →+* chig₀.range :=
      e.symm.toRingHom.comp (χε.codRestrict iota₀.range hrange) with hψ₀def
    have hψ₀ : ∀ t, iota₀ (ψ₀ t) = χε t := by
      intro t
      have h1 : (e (ψ₀ t) : F) = iota₀ (ψ₀ t) := rfl
      rw [← h1, hψ₀def, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply]
      rfl
    set ψ : heckeAlgebra (N * r) 2 (↑S : Set ℕ) →+* ℂ := chig₀.range.subtype.comp ψ₀ with hψdef
    have hψapply : ∀ t, ψ t = (ψ₀ t : ℂ) := fun t => rfl
    have hkerψ : ∀ t, χε t = 0 ↔ ψ t = 0 := by
      intro t
      rw [hψapply, ← hψ₀ t]
      constructor
      · intro h
        have h' : ψ₀ t = 0 := hiota_inj (by rw [h, map_zero])
        rw [h']; rfl
      · intro h
        have h' : ψ₀ t = 0 := Subtype.ext h
        rw [h', map_zero]
    have hψT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ N * r) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        ψ (heckeAlgebra.T hℓ hℓL hℓS) = qCoeff g₀ ℓ := by
      intro ℓ hℓ hℓL hℓS
      have hℓN : ¬ ℓ ∣ N := fun h => hℓL (h.mul_right r)
      have hℓr : ℓ ≠ r := fun h => hℓL (h ▸ dvd_mul_left r N)
      have hℓM₀ : ¬ ℓ ∣ M₀ := fun h => hℓN (h.trans hM₀N)
      have h1 : ψ₀ (heckeAlgebra.T hℓ hℓL hℓS) = chig₀.rangeRestrict (heckeAlgebra.T hℓ hℓM₀ hℓS) := by
        apply hiota_inj
        rw [hψ₀, hχεT ℓ hℓ hℓL hℓS, haF_of_ne ℓ hℓ hℓN hℓS hℓr, ← hiota₀ ℓ hℓ hℓN hℓS]
      rw [hψapply, h1, RingHom.coe_rangeRestrict, hchig₀ ℓ hℓ hℓM₀ hℓS]
    have hψU : ψ (heckeAlgebra.U hr (dvd_mul_left r N) hrS) = (ε : ℂ) := by
      have h1 : ψ₀ (heckeAlgebra.U hr (dvd_mul_left r N) hrS) = (ε : chig₀.range) := by
        apply hiota_inj
        rw [hψ₀, hχεU r hr (dvd_mul_left r N) hrS, haF_r, map_intCast]
      rw [hψapply, h1]
      rfl

    obtain ⟨c', hc'par, hc'0, hc'T, hc'U⟩ := hdesc ℂ ψ hkerψ

    obtain ⟨ES, -, hinj, hrangeES, hEST, hESU⟩ := CohCarrier.exists_eichlerShimura_H1_top (N * r)
    have hc'range : c' ∈ LinearMap.range ES := by rw [hrangeES]; exact hc'par
    obtain ⟨fg, hfg⟩ := hc'range
    have hfg0 : fg ≠ 0 := by
      rintro rfl
      exact hc'0 (by rw [← hfg, map_zero])
    have hfgT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ N * r) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        CuspForm.heckeTLin 2 hℓ hℓL fg.1 = qCoeff g₀ ℓ • fg.1 ∧
          CuspForm.heckeTLin 2 hℓ hℓL fg.2 = qCoeff g₀ ℓ • fg.2 := by
      intro ℓ hℓ hℓL hℓS
      have h := hEST ℓ hℓ hℓL fg.1 fg.2
      rw [Prod.mk.eta, hfg, hc'T ℓ hℓ hℓL hℓS, hψT ℓ hℓ hℓL hℓS, ← hfg, ← map_smul] at h
      have h' := hinj h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    have hfgU : CuspForm.heckeULin 2 (dvd_mul_left r N) fg.1 = (ε : ℂ) • fg.1 ∧
        CuspForm.heckeULin 2 (dvd_mul_left r N) fg.2 = (ε : ℂ) • fg.2 := by
      have h := hESU r hr (dvd_mul_left r N) fg.1 fg.2
      rw [Prod.mk.eta, hfg, hc'U r hr (dvd_mul_left r N) hrS, hψU, ← hfg, ← map_smul] at h
      have h' := hinj h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

    have hquad : ((ε : ℂ)) ^ 2 - qCoeff g₀ r * (ε : ℂ) + r = 0 := by
      by_cases hf : fg.1 = 0
      · have hg : fg.2 ≠ 0 := by
          intro hg; apply hfg0; exact Prod.ext hf hg
        exact CuspForm.sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform N r hr hrN S
          M₀ hM₀N g₀ hg₀ fg.2 hg (fun ℓ hℓ hℓL hℓS => (hfgT ℓ hℓ hℓL hℓS).2) (ε : ℂ) hfgU.2
      · exact CuspForm.sq_sub_qCoeff_mul_add_eq_zero_of_heckeULin_eq_smul_of_isNewform N r hr hrN S
          M₀ hM₀N g₀ hg₀ fg.1 hf (fun ℓ hℓ hℓL hℓS => (hfgT ℓ hℓ hℓL hℓS).1) (ε : ℂ) hfgU.1

    have hsqC : qCoeff g₀ r ^ 2 = ((r : ℂ) + 1) ^ 2 := by
      rcases hε with rfl | rfl
      · push_cast at hquad
        have ha : qCoeff g₀ r = (r : ℂ) + 1 := by linear_combination -hquad
        rw [ha]
      · push_cast at hquad
        have ha : qCoeff g₀ r = -((r : ℂ) + 1) := by linear_combination hquad
        rw [ha]; ring

    set x : chig₀.range := chig₀.rangeRestrict (heckeAlgebra.T hr hrM₀ hrS) with hxdef
    have hxC : (x : ℂ) = qCoeff g₀ r := by
      rw [hxdef, RingHom.coe_rangeRestrict, hchig₀ r hr hrM₀ hrS]
    have hxsq : x ^ 2 = ((r : chig₀.range) + 1) ^ 2 := by
      apply Subtype.ext
      push_cast
      rw [hxC, hsqC]
    have hxF : iota₀ x = χ (heckeAlgebra.T hr hrN hrS) := hiota₀ r hr hrN hrS
    apply hχr
    rw [← hxF, ← map_pow, hxsq]
    simp

  have h1 := main 1 (Or.inl rfl)
  have h2 := main (-1) (Or.inr rfl)
  push_cast at h1 h2
  rw [one_smul] at h1
  rw [neg_one_smul] at h2
  have h : (2 : F) • c = 0 := by
    have := congrArg₂ (· + ·) h1 h2
    simp only [add_zero] at this
    rw [two_smul]
    calc c + c = (c + U c) + (c + -U c) := by abel
      _ = 0 := this
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

end S_CohCarrier_eq_zero_of_mem_parabolicHoms_of_jDeg_eq_zero_of_apply_T_sq_ne
end P2MW
export P2MW.S_CohCarrier_eq_zero_of_mem_parabolicHoms_of_jDeg_eq_zero_of_apply_T_sq_ne (solution)

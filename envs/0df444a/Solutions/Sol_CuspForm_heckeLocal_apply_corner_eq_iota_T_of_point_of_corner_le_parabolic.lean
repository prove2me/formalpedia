-- Prove2me | solution 1 for CuspForm.heckeLocal.apply_corner_eq_iota_T_of_point_of_corner_le_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/28824688-f510-5ee4-aa4f-044f96f5309a

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_exists_mvPolynomial_heckeT_eigenvalue_of_mem_parabolicHoms_gammaH_top
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ne_zero_mem_parabolicHoms_gammaH_heckeT_eq_qCoeff_smul
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_apply_corner_eq_iota_T_of_point_of_corner_le_parabolic
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe"
p2m_attr_erase "simp" "ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower

namespace C2Sol

theorem injective_of_isIntegral_int {R 𝒪 : Type} [CommRing R] [IsDomain R] [Algebra.IsIntegral ℤ R]
    [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (f : R →+* 𝒪) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro z hz
  simp only [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hz
  rw [Ideal.mem_bot]
  exact hz

theorem algebraIsIntegral_int_of_surjective {A R : Type} [CommRing A] [CommRing R]
    [Algebra.IsIntegral ℤ A] (φ : A →+* R) (hφ : Function.Surjective φ) :
    Algebra.IsIntegral ℤ R := by
  refine ⟨fun r => ?_⟩
  obtain ⟨a, rfl⟩ := hφ r
  obtain ⟨f, hfm, hf⟩ : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
  refine ⟨f, hfm, ?_⟩
  have := congrArg φ hf
  rwa [Polynomial.hom_eval₂, map_zero, RingHom.ext_int (φ.comp _) (algebraMap ℤ R)] at this

theorem heckeT_smul (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A : Type} [CommRing A] (ℓ : ℕ) [NeZero ℓ]
    (c : A) (φ : H1 M H A) : heckeT M H ℓ A (c • φ) = c • heckeT M H ℓ A φ := by
  have h1 : ∀ ψ : H1 M H A, c • ψ = (AddMonoidHom.mulLeft c).comp ψ := fun ψ => by
    ext x; rfl
  rw [h1, h1, CohCarrier.heckeT_comp_coeff]

theorem iDeg'_one_injective (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {A : Type} [CommRing A] [IsDomain A]
    [CharZero A] (h1 : LevelLE M M ⊤ H 1) (φ : H1 M ⊤ A) (h0 : iDeg' M M ⊤ H 1 A h1 φ = 0) : φ = 0 := by
  classical
  ext γ
  have hidx : ((iotaDeg M M ⊤ H 1 h1).range).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨n, hn, -, hγn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx (Additive.toMul γ)
  obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.mp hγn
  have hval : (iDeg' M M ⊤ H 1 A h1 φ) (Additive.ofMul δ) = 0 := by rw [h0]; rfl
  have hval' : φ (Additive.ofMul (iotaDeg M M ⊤ H 1 h1 δ)) = 0 := hval
  rw [hδ, ofMul_pow, map_nsmul] at hval'
  have h2 : φ γ = 0 := by
    have h3 : (n : A) * φ γ = 0 := by simpa [nsmul_eq_mul] using hval'
    exact (mul_eq_zero.mp h3).resolve_left (Nat.cast_ne_zero.mpr hn.ne')
  simp at h2 ⊢
  exact h2

end C2Sol

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
open C2Sol CuspForm in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (S : Finset ℕ) (hpS : p ∈ S)
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (r : ℕ) (hr : r.Prime) (hrN : ¬ r ∣ N * p) [NeZero (N * r)] (H₀ : Subgroup (ZMod (N * r))ˣ)
    (h₁₀ : LevelLE (N * r) (N * r) ⊤ H₀ 1)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (πT₀ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] 𝒪)
    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 (N * r) H₀ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 (N * r) H₀ 𝒪)]
    (cd₀ : H1CornerData (𝒪 := 𝒪) (N * r) H₀ 𝒪 𝕋₀)
    (e₀ : cd₀.cornerRing ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
    (hT : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r)
        (m : cd₀.cornerModule),
      ((e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
          : cd₀.cornerModule) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ ℓ 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (tp : cd₀.cornerRing)
    (htp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; ∀ m : cd₀.cornerModule,
      ((tp • m : cd₀.cornerModule) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (hocc : Submodule.torsionBySet cd₀.cornerRing cd₀.cornerModule ↑(RingHom.ker (πT₀.comp e₀.toAlgHom)) ≠ ⊥)
    (hW₀ : ∀ v : H1 (N * r) H₀ 𝒪, v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (cd₀.split.e cd₀.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * r) ⊤) 𝒪).map (iDegL (N * r) (N * r) ⊤ H₀ 1 𝒪 𝒪 h₁₀))

    (M : ℕ) [NeZero M] (hMN : M ∣ N) (hpM : ¬ p ∣ M)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra M 2 ((↑S : Set ℕ) \ {p}) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* 𝒪)
    (hiota : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
        (fun h => hℓN (h.trans hMN)) (fun h => hℓS (Set.mem_of_mem_diff h)))) =
        πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) :
    πT₀ (e₀ tp) =
      iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpM (fun h => h.2 rfl))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hNr0 : N * r ≠ 0 := NeZero.ne _
  have hpNr : ¬ p ∣ N * r := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hpN h
    · have : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp h
      exact hrN (this ▸ dvd_mul_left p N)

  obtain ⟨m, hm, hm0⟩ := (Submodule.ne_bot_iff _).mp hocc
  have hscalar : ∀ x : cd₀.cornerRing, x • m = (πT₀ (e₀ x)) • m := by
    intro x
    have hx : x - algebraMap 𝒪 cd₀.cornerRing (πT₀ (e₀ x)) ∈
        (↑(RingHom.ker (πT₀.comp e₀.toAlgHom)) : Set cd₀.cornerRing) := by
      show x - _ ∈ RingHom.ker (πT₀.comp e₀.toAlgHom)
      rw [RingHom.mem_ker, map_sub]
      show πT₀ (e₀ x) - πT₀ (e₀ (algebraMap 𝒪 cd₀.cornerRing (πT₀ (e₀ x)))) = 0
      rw [AlgEquiv.commutes, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h0 := (Submodule.mem_torsionBySet_iff _ _).mp hm ⟨_, hx⟩
    simp only [sub_smul, sub_eq_zero] at h0
    rw [h0, algebraMap_smul]

  set v : H1 (N * r) H₀ 𝒪 := (m : H1 (N * r) H₀ 𝒪) with hv
  have hv0 : v ≠ 0 := fun h => hm0 (Subtype.ext h)
  have heigT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ¬ ℓ ∣ N * r) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      heckeT (N * r) H₀ ℓ 𝒪 v =
        πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀
          (CuspForm.heckeAlgebra.T hℓ (fun h => hℓr (h.mul_right r)) hℓS)) • v := by
    intro ℓ hℓ hℓr hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓN : ¬ ℓ ∣ N := fun h => hℓr (h.mul_right r)
    have h1 := hT ℓ hℓ hℓN hℓS hℓr m
    rw [hscalar, AlgEquiv.apply_symm_apply] at h1
    rw [← h1, Submodule.coe_smul_of_tower]
  have heigp : heckeT (N * r) H₀ p 𝒪 v = πT₀ (e₀ tp) • v := by
    have h1 := htp m
    rw [hscalar] at h1
    rw [← h1, Submodule.coe_smul_of_tower]

  obtain ⟨w₀, hw₀par, hw₀v⟩ := Submodule.mem_map.mp (hW₀ v m.2)
  have hιeq : ∀ φ : H1 (N * r) ⊤ 𝒪,
      iDegL (N * r) (N * r) ⊤ H₀ 1 𝒪 𝒪 h₁₀ φ = iDeg' (N * r) (N * r) ⊤ H₀ 1 𝒪 h₁₀ φ := fun _ => rfl
  have hw₀v' : iDeg' (N * r) (N * r) ⊤ H₀ 1 𝒪 h₁₀ w₀ = v := by rw [← hιeq]; exact hw₀v
  have hw₀0 : w₀ ≠ 0 := by
    intro h
    apply hv0
    rw [← hw₀v', h, map_zero]

  have htrans : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ¬ ℓ ∣ N * r) (c : 𝒪),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      heckeT (N * r) H₀ ℓ 𝒪 v = c • v → heckeT (N * r) ⊤ ℓ 𝒪 w₀ = c • w₀ := by
    intro ℓ hℓ hℓr c hvc
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have key : iDeg' (N * r) (N * r) ⊤ H₀ 1 𝒪 h₁₀ (heckeT (N * r) ⊤ ℓ 𝒪 w₀ - c • w₀) = 0 := by
      rw [map_sub, CohCarrier.iDeg_heckeT_comm_of_coprime h₁₀ (Nat.coprime_one_right ℓ) hℓ hℓr w₀, hw₀v', hvc,
        ← hw₀v', ← hιeq, ← hιeq, map_smul, sub_self]
    exact sub_eq_zero.mp (iDeg'_one_injective (N * r) H₀ h₁₀ _ key)
  have hw₀T : ∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ (↑S : Set ℕ) ∧ ¬ ℓ ∣ N * r},
      haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
      heckeT (N * r) ⊤ ℓ.1 𝒪 w₀ =
        πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀
          (CuspForm.heckeAlgebra.T ℓ.2.1 (fun h => ℓ.2.2.2 (h.mul_right r)) ℓ.2.2.1)) • w₀ := by
    rintro ⟨ℓ, hℓ, hℓS, hℓr⟩
    exact htrans ℓ hℓ hℓr _ (heigT ℓ hℓ hℓr hℓS)
  have hw₀p : heckeT (N * r) ⊤ p 𝒪 w₀ = πT₀ (e₀ tp) • w₀ := htrans p hp hpNr _ heigp

  haveI : Module.Finite ℤ (heckeAlgebra M 2 ((↑S : Set ℕ) \ {p})) :=
    (CuspForm.hasIntegralStructure_two M).moduleFinite_heckeAlgebra (by norm_num) _
  haveI : Algebra.IsIntegral ℤ chig.range :=
    algebraIsIntegral_int_of_surjective chig.rangeRestrict chig.rangeRestrict_surjective
  have hxval : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
      ((chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) : chig.range) : ℂ) =
        ModularFormClass.qCoeff g ℓ := fun ℓ hℓ hℓM hℓS => hchig ℓ hℓ hℓM hℓS

  obtain ⟨n, hn, P, hP⟩ :=
    CohCarrier.exists_mvPolynomial_heckeT_eigenvalue_of_mem_parabolicHoms_gammaH_top (N * r) (↑S : Set ℕ)
      S.finite_toSet hp hpNr
  have h𝒪 := hP 𝒪 w₀ hw₀par hw₀0 _ _ hw₀T hw₀p
  obtain ⟨w, hw0, hwpar, hwT⟩ :=
    hg.isNormalizedEigenform.exists_ne_zero_mem_parabolicHoms_gammaH_heckeT_eq_qCoeff_smul (N * r)
      (hMN.trans (dvd_mul_right N r)) ⊤
  have hℂ := hP ℂ w hwpar hw0 (fun ℓ => ModularFormClass.qCoeff g ℓ.1) (ModularFormClass.qCoeff g p)
    (fun ℓ => hwT ℓ.1 ℓ.2.1 ℓ.2.2.2) (hwT p hp hpNr)

  let x : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ (↑S : Set ℕ) ∧ ¬ ℓ ∣ N * r} → chig.range := fun ℓ =>
    chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 (fun h => ℓ.2.2.2 ((h.trans hMN).mul_right r))
      (fun h => ℓ.2.2.1 (Set.mem_of_mem_diff h)))
  let xp : chig.range := chig.rangeRestrict (CuspForm.heckeAlgebra.T hp hpM (fun h => h.2 rfl))
  have hxℂ : (fun ℓ => ((x ℓ : chig.range) : ℂ)) = fun ℓ => ModularFormClass.qCoeff g ℓ.1 := by
    funext ℓ; exact hxval _ _ _ _
  have hxpℂ : ((xp : chig.range) : ℂ) = ModularFormClass.qCoeff g p := hxval _ _ _ _
  have hx𝒪 : (fun ℓ => iota (x ℓ)) = fun ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ (↑S : Set ℕ) ∧ ¬ ℓ ∣ N * r} =>
      πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀
        (CuspForm.heckeAlgebra.T ℓ.2.1 (fun h => ℓ.2.2.2 (h.mul_right r)) ℓ.2.2.1)) := by
    funext ℓ
    exact hiota ℓ.1 ℓ.2.1 (fun h => ℓ.2.2.2 (h.mul_right r)) ℓ.2.2.1

  have hR : (n : chig.range) * xp = MvPolynomial.aeval x P := by
    apply Subtype.ext
    have h1 : (((MvPolynomial.aeval x P : chig.range)) : ℂ) =
        MvPolynomial.aeval (fun ℓ => ((x ℓ : chig.range) : ℂ)) P := by
      rw [show ((MvPolynomial.aeval x P : chig.range) : ℂ) = chig.range.subtype (MvPolynomial.aeval x P)
        from rfl, MvPolynomial.map_aeval]
      rw [MvPolynomial.aeval_def]
      show MvPolynomial.eval₂ _ _ P = _
      rw [RingHom.ext_int ((chig.range.subtype).comp (algebraMap ℤ _)) (algebraMap ℤ ℂ)]
      rfl
    rw [h1, hxℂ, ← hℂ]
    show ((n : chig.range) : ℂ) * (xp : ℂ) = (n : ℂ) * ModularFormClass.qCoeff g p
    rw [hxpℂ]
    simp

  have h𝒪' : (n : 𝒪) * iota xp = (n : 𝒪) * πT₀ (e₀ tp) := by
    rw [h𝒪, ← hx𝒪]
    have := congrArg iota hR
    rw [map_mul, map_natCast] at this
    rw [this, MvPolynomial.map_aeval, MvPolynomial.aeval_def]
    show MvPolynomial.eval₂ _ _ P = _
    rw [RingHom.ext_int (iota.comp (algebraMap ℤ _)) (algebraMap ℤ 𝒪)]
  have hnO : (n : 𝒪) ≠ 0 := Nat.cast_ne_zero.mpr hn
  exact (mul_left_cancel₀ hnO h𝒪').symm

end S_CuspForm_heckeLocal_apply_corner_eq_iota_T_of_point_of_corner_le_parabolic
end P2MW
export P2MW.S_CuspForm_heckeLocal_apply_corner_eq_iota_T_of_point_of_corner_le_parabolic (solution)

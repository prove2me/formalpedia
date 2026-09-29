-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_ringHom_extension_apply_U_eq_zero_and_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/43862365-25a6-5aaf-af64-d8bc8b7a1c79

import Theorems.Thm_CuspForm_exists_isNewform_point_factor
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra_integralClosure
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CuspForm_forall_exists_qCoeff_eq_of_isNormalizedEigenform
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import Theorems.Thm_CuspForm_qCoeff_sq_eq_one_of_isNewform
import Theorems.Thm_IntegralClosure_exists_extend_ringHom_dvr_finite
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_extension_apply_U_eq_zero_and_dvd
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_heckeULowerLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_traceLin_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000

noncomputable section

namespace K1RE1

open IsLocalRing CuspForm ModularFormClass

theorem ringHom_ext {N : ℕ} [NeZero N] {S : Set ℕ} {B : Type} [NonAssocRing B]
    {F G : heckeAlgebra N 2 S →+* B}
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      F (heckeAlgebra.T hℓ hℓN hℓS) = G (heckeAlgebra.T hℓ hℓN hℓS))
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
      F (heckeAlgebra.U hq hqN hqS) = G (heckeAlgebra.U hq hqN hqS)) :
    F = G := by
  refine RingHom.ext fun t => ?_
  obtain ⟨x, hx⟩ := t
  have hx' : x ∈ Algebra.adjoin ℤ (heckeGenerators N 2 S) := hx
  induction hx' using Algebra.adjoin_induction with
  | mem x h =>
    rcases h with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
    · exact hT ℓ hℓ hℓN hℓS
    · exact hU q hq hqN hqS
  | algebraMap r =>
    have h : (⟨algebraMap ℤ _ r, hx⟩ : heckeAlgebra N 2 S) = (r : heckeAlgebra N 2 S) := by
      apply Subtype.ext
      simp
    rw [h, map_intCast, map_intCast]
  | add x y hx'' hy'' ihx ihy =>
    have h : (⟨x + y, hx⟩ : heckeAlgebra N 2 S) = ⟨x, hx''⟩ + ⟨y, hy''⟩ := rfl
    rw [h, map_add, map_add, ihx hx'', ihy hy'']
  | mul x y hx'' hy'' ihx ihy =>
    have h : (⟨x * y, hx⟩ : heckeAlgebra N 2 S) = ⟨x, hx''⟩ * ⟨y, hy''⟩ := rfl
    rw [h, map_mul, map_mul, ihx hx'', ihy hy'']

theorem exists_prime_natCast_mem_maximalIdeal (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [Finite (ResidueField 𝒪)] :
    ∃ p : ℕ, p.Prime ∧ (p : 𝒪) ∈ maximalIdeal 𝒪 := by
  obtain ⟨p, hpchar⟩ := CharP.exists (ResidueField 𝒪)
  haveI := hpchar
  refine ⟨p, CharP.char_is_prime (ResidueField 𝒪) p, ?_⟩
  rw [← residue_eq_zero_iff, map_natCast]
  exact CharP.cast_eq_zero (ResidueField 𝒪) p

theorem exists_root_quadratic (b c : ℂ) : ∃ a : ℂ, a ^ 2 - b * a + c = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (b ^ 2 - 4 * c) (by norm_num : 0 < 2)
  exact ⟨(b + s) / 2, by linear_combination hs / 4⟩

theorem main
    (N : ℕ) [NeZero N] (S S₀ : Finset ℕ) (hS₀ : S₀ ⊆ S)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪') :
    ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
      (_ : IsAdicComplete (maximalIdeal 𝒪'') 𝒪'') (_ : Finite (ResidueField 𝒪''))
      (_ : CharZero 𝒪'') (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'')
      (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
    Function.Injective (algebraMap 𝒪' 𝒪'') ∧
    ∃ χ' : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* 𝒪'',
      (∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
        χ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t) =
          algebraMap 𝒪' 𝒪'' (χ t)) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)), q ^ 2 ∣ N →
        χ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = 0) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)), ¬ q ^ 2 ∣ N →
        χ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) ∣ (q : 𝒪'')) := by
  classical
  have hS₀' : (↑S₀ : Set ℕ) ⊆ ↑S := Finset.coe_subset.mpr hS₀

  obtain ⟨p, hp, hp𝒪'⟩ := exists_prime_natCast_mem_maximalIdeal 𝒪'

  obtain ⟨M, _instM, hMN, f, hf, chig, hchig, iota, hiota⟩ :=
    CuspForm.exists_isNewform_point_factor N S hNS 𝒪' χ
  have hNS_M : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S := fun q hq hqM => hNS q hq (hqM.trans hMN)

  choose α hα using fun q : ℕ => exists_root_quadratic (qCoeff f q) (q : ℂ)

  obtain ⟨g, hg, hgℓ, hg_eq, hg_root, hg_zero⟩ :=
    hf.isNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
      hMN α (fun q _ _ _ _ => hα q)

  obtain ⟨χf, hχf⟩ := hf.isNormalizedEigenform.exists_ringHom_heckeAlgebra_integralClosure
    (CuspForm.hasIntegralStructure_two M) (↑S : Set ℕ)
  obtain ⟨χg, hχg⟩ := hg.exists_ringHom_heckeAlgebra_integralClosure
    (CuspForm.hasIntegralStructure_two N) (↑S₀ : Set ℕ)
  obtain ⟨χfℂ, hχfℂ, hχfℂT, -⟩ := hf.isNormalizedEigenform.exists_ringHom_heckeAlgebra (↑S : Set ℕ)
  obtain ⟨χgℂ, hχgℂ, hχgℂT, hχgℂU⟩ := hg.exists_ringHom_heckeAlgebra (↑S₀ : Set ℕ)
  have hχf_val : ∀ t, ((χf t : integralClosure ℤ ℂ) : ℂ) = χfℂ t := fun t =>
    smul_left_injective ℂ hf.ne_zero ((hχf t).symm.trans (hχfℂ t))
  have hχg_val : ∀ t, ((χg t : integralClosure ℤ ℂ) : ℂ) = χgℂ t := fun t =>
    smul_left_injective ℂ hg.ne_zero ((hχg t).symm.trans (hχgℂ t))

  have hchig_eq : chig = χfℂ := by
    refine ringHom_ext (fun ℓ hℓ hℓM hℓS => ?_) (fun q hq hqM hqS => absurd (hNS_M q hq hqM) hqS)
    rw [hchig ℓ hℓ hℓM hℓS, hχfℂT ℓ hℓ hℓM hℓS]

  set R : Subalgebra ℤ (integralClosure ℤ ℂ) := χf.toIntAlgHom.range with hRdef
  have hRmem : ∀ x : R, ((x : integralClosure ℤ ℂ) : ℂ) ∈ chig.range := by
    rintro ⟨_, t, rfl⟩
    refine ⟨t, ?_⟩
    rw [hchig_eq, ← hχf_val]
    rfl
  set φ₀ : R →+* chig.range :=
    (((integralClosure ℤ ℂ).val.toRingHom).comp R.val.toRingHom).codRestrict chig.range hRmem
    with hφ₀def
  set φ : R →+* 𝒪' := iota.comp φ₀ with hφdef

  haveI : Module.Finite ℤ (heckeAlgebra N 2 (↑S₀ : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two N (↑S₀ : Set ℕ)
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := ℤ) (M := heckeAlgebra N 2 (↑S₀ : Set ℕ))
  choose af haf using fun q : ℕ => CuspForm.forall_exists_qCoeff_eq_of_isNormalizedEigenform
    hf.isNormalizedEigenform q
  set s : Finset (integralClosure ℤ ℂ) := G.image χg ∪ N.primeFactors.image af with hsdef
  set R' : Subalgebra ℤ (integralClosure ℤ ℂ) := R ⊔ Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ))
    with hR'def

  obtain ⟨𝒪'', _, _, _, _, _, _, _, _, _, -, hinj, φ', hφ'⟩ :=
    IntegralClosure.exists_extend_ringHom_dvr_finite hp𝒪' R s φ

  have hs_sub : (↑s : Set (integralClosure ℤ ℂ)) ⊆ R' := fun x hx =>
    (le_sup_right : Algebra.adjoin ℤ (↑s : Set (integralClosure ℤ ℂ)) ≤ R') (Algebra.subset_adjoin hx)
  have hmem : ∀ t : heckeAlgebra N 2 (↑S₀ : Set ℕ), χg t ∈ R' := by
    intro t
    have ht : t ∈ Submodule.span ℤ (↑G : Set (heckeAlgebra N 2 (↑S₀ : Set ℕ))) := by
      rw [hG]; exact Submodule.mem_top
    induction ht using Submodule.span_induction with
    | mem x hx =>
      exact hs_sub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul n x _ hx => rw [map_zsmul]; exact zsmul_mem hx n
  have haf_mem : ∀ q : ℕ, q.Prime → q ∣ N → af q ∈ R' := fun q hq hqN =>
    hs_sub (Finset.mem_coe.mpr (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩))))
  set χ' : heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* 𝒪'' := φ'.comp (χg.codRestrict R' hmem) with hχ'def
  have hχ'_apply : ∀ t, χ' t = φ' ⟨χg t, hmem t⟩ := fun t => rfl

  have hφ'_R : ∀ (x : integralClosure ℤ ℂ) (hxR : x ∈ R) (hxR' : x ∈ R'),
      φ' ⟨x, hxR'⟩ = algebraMap 𝒪' 𝒪'' (φ ⟨x, hxR⟩) := by
    intro x hxR hxR'
    rw [← hφ' ⟨x, hxR⟩]
    rfl
  refine ⟨𝒪'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hinj, χ', ?_, ?_, ?_⟩
  ·
    intro t
    have key : χ'.comp (Subalgebra.inclusion (heckeAlgebra_mono hS₀')).toRingHom =
        (algebraMap 𝒪' 𝒪'').comp χ := by
      refine ringHom_ext (fun ℓ hℓ hℓN hℓS => ?_) (fun q hq hqN hqS => absurd (hNS q hq hqN) hqS)
      have hℓM : ¬ ℓ ∣ M := fun h => hℓN (h.trans hMN)
      have hℓS₀ : ℓ ∉ (↑S₀ : Set ℕ) := fun h => hℓS (hS₀' h)

      have hincl : Subalgebra.inclusion (heckeAlgebra_mono hS₀')
          (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N 2 (↑S : Set ℕ)) =
          heckeAlgebra.T hℓ hℓN hℓS₀ := Subtype.ext rfl

      have hval : χg (heckeAlgebra.T hℓ hℓN hℓS₀) = χf (heckeAlgebra.T hℓ hℓM hℓS) := by
        apply Subtype.ext
        rw [hχg_val, hχf_val, hχgℂT ℓ hℓ hℓN hℓS₀, hχfℂT ℓ hℓ hℓM hℓS, hgℓ ℓ hℓ hℓN]
      have hxR : χf (heckeAlgebra.T hℓ hℓM hℓS) ∈ R := ⟨heckeAlgebra.T hℓ hℓM hℓS, rfl⟩
      rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        hincl]
      change φ' ⟨χg (heckeAlgebra.T hℓ hℓN hℓS₀), hmem _⟩ = algebraMap 𝒪' 𝒪'' (χ (heckeAlgebra.T hℓ hℓN hℓS))
      have h1 : (⟨χg (heckeAlgebra.T hℓ hℓN hℓS₀), hmem _⟩ : R') =
          ⟨χf (heckeAlgebra.T hℓ hℓM hℓS), hval ▸ hmem _⟩ := Subtype.ext hval
      rw [h1, hφ'_R _ hxR]
      congr 1

      rw [← hiota ℓ hℓ hℓN hℓS, hφdef, RingHom.comp_apply]
      congr 1
      apply Subtype.ext
      change ((χf (heckeAlgebra.T hℓ hℓM hℓS) : integralClosure ℤ ℂ) : ℂ) = chig _
      rw [hχf_val, hchig_eq]
    exact DFunLike.congr_fun key t
  ·
    intro q hq hqN hqS₀ hsq
    have hval0 : χg (heckeAlgebra.U hq hqN hqS₀) = 0 := by
      apply Subtype.ext
      rw [hχg_val, hχgℂU q hq hqN hqS₀, ZeroMemClass.coe_zero]
      have hle : M.factorization q ≤ N.factorization q :=
        (Nat.factorization_le_iff_dvd (NeZero.ne M) (NeZero.ne N)).mpr hMN q
      rcases hle.lt_or_eq with hlt | heq
      · exact hg_zero q hq hsq hlt
      · rw [hg_eq q hq hqN heq.symm]
        have h2 : 2 ≤ N.factorization q := (hq.pow_dvd_iff_le_factorization (NeZero.ne N)).mp hsq
        have hsqM : q ^ 2 ∣ M := (hq.pow_dvd_iff_le_factorization (NeZero.ne M)).mpr (heq ▸ h2)
        exact CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hf q hq hsqM
    rw [hχ'_apply]
    have h1 : (⟨χg (heckeAlgebra.U hq hqN hqS₀), hmem _⟩ : R') = 0 := Subtype.ext hval0
    rw [h1, map_zero]
  ·
    intro q hq hqN hqS₀ hnsq

    set ev : R' →+* ℂ := (integralClosure ℤ ℂ).val.toRingHom.comp R'.val.toRingHom with hevdef
    have hev_inj : Function.Injective ev := Subtype.val_injective.comp Subtype.val_injective
    have hev : ∀ y : R', ev y = ((y : integralClosure ℤ ℂ) : ℂ) := fun y => rfl
    set x : R' := ⟨χg (heckeAlgebra.U hq hqN hqS₀), hmem _⟩ with hxdef
    have hx : ev x = qCoeff g q := by rw [hev, hχg_val, hχgℂU q hq hqN hqS₀]
    have hvN : N.factorization q = 1 := by
      have h1 : 1 ≤ N.factorization q :=
        (hq.pow_dvd_iff_le_factorization (NeZero.ne N)).mp ((pow_one q).symm ▸ hqN)
      have h2 : ¬ 2 ≤ N.factorization q := fun h =>
        hnsq ((hq.pow_dvd_iff_le_factorization (NeZero.ne N)).mpr h)
      omega
    rw [hχ'_apply, ← hxdef]
    by_cases hqM : q ∣ M
    ·
      have hnsqM : ¬ q ^ 2 ∣ M := fun h => hnsq (h.trans hMN)
      have hvM : M.factorization q = 1 := by
        have h1 : 1 ≤ M.factorization q :=
          (hq.pow_dvd_iff_le_factorization (NeZero.ne M)).mp ((pow_one q).symm ▸ hqM)
        have h2 : ¬ 2 ≤ M.factorization q := fun h =>
          hnsqM ((hq.pow_dvd_iff_le_factorization (NeZero.ne M)).mpr h)
        omega
      have hsq1 : x ^ 2 = 1 := hev_inj (by
        rw [map_pow, map_one, hx, hg_eq q hq hqN (hvN.trans hvM.symm)]
        exact CuspForm.qCoeff_sq_eq_one_of_isNewform hf q hq hqM hnsqM)
      refine ⟨φ' x * q, ?_⟩
      rw [← mul_assoc, ← sq, ← map_pow, hsq1, map_one, one_mul]
    ·
      set a : R' := ⟨af q, haf_mem q hq hqN⟩ with hadef
      have ha : ev a = qCoeff f q := by rw [hev]; exact haf q
      have hprod : x * (a - x) = (q : R') := hev_inj (by
        rw [map_mul, map_sub, map_natCast, hx, ha, hg_root q hq hqN hqM hnsq]
        linear_combination (-1 : ℂ) * hα q)
      refine ⟨φ' (a - x), ?_⟩
      rw [← map_mul, hprod, map_natCast]

end K1RE1

end

open IsLocalRing in
theorem solution
    (N : ℕ) [NeZero N] (S S₀ : Finset ℕ) (hS₀ : S₀ ⊆ S)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    [IsAdicComplete (maximalIdeal 𝒪') 𝒪'] [Finite (ResidueField 𝒪')] [CharZero 𝒪']
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪') :
    ∃ (𝒪'' : Type) (_ : CommRing 𝒪'') (_ : IsDomain 𝒪'') (_ : IsDiscreteValuationRing 𝒪'')
      (_ : IsAdicComplete (maximalIdeal 𝒪'') 𝒪'') (_ : Finite (ResidueField 𝒪''))
      (_ : CharZero 𝒪'') (_ : Algebra 𝒪' 𝒪'') (_ : Module.Finite 𝒪' 𝒪'')
      (_ : IsLocalHom (algebraMap 𝒪' 𝒪'')),
    Function.Injective (algebraMap 𝒪' 𝒪'') ∧
    ∃ χ' : CuspForm.heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* 𝒪'',
      (∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
        χ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t) =
          algebraMap 𝒪' 𝒪'' (χ t)) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)), q ^ 2 ∣ N →
        χ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) = 0) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS₀ : q ∉ (↑S₀ : Set ℕ)), ¬ q ^ 2 ∣ N →
        χ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) ∣ (q : 𝒪'')) :=
  K1RE1.main N S S₀ hS₀ hNS 𝒪' χ

end S_CuspForm_heckeAlgebra_exists_ringHom_extension_apply_U_eq_zero_and_dvd
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_extension_apply_U_eq_zero_and_dvd (solution)

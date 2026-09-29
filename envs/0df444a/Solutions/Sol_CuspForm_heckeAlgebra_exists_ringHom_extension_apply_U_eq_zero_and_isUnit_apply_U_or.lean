-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_ringHom_extension_apply_U_eq_zero_and_isUnit_apply_U_or
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7519736b-0a64-55b4-8c70-bdb6c07f755b

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

namespace P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_extension_apply_U_eq_zero_and_isUnit_apply_U_or
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
set_option maxHeartbeats 6400000

noncomputable section

namespace K1EE1

open IsLocalRing CuspForm ModularFormClass Polynomial

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

theorem isIntegral_of_root (a : integralClosure ℤ ℂ) (q : ℕ) (x : ℂ)
    (hx : x ^ 2 - (a : ℂ) * x + q = 0) : IsIntegral ℤ x := by
  have hmon : (X ^ 2 - C a * X + C (q : integralClosure ℤ ℂ) : (integralClosure ℤ ℂ)[X]).Monic := by
    have hre : (X ^ 2 - C a * X + C (q : integralClosure ℤ ℂ) : (integralClosure ℤ ℂ)[X]) =
        X ^ 2 + (C (q : integralClosure ℤ ℂ) - C a * X) := by ring
    rw [hre]
    refine (monic_X_pow 2).add_of_left ?_
    calc degree (C (q : integralClosure ℤ ℂ) - C a * X) ≤ 1 := by
            refine (degree_sub_le _ _).trans (max_le ?_ ?_)
            · exact degree_C_le.trans (by norm_num)
            · exact degree_C_mul_X_le a
      _ < degree ((X : (integralClosure ℤ ℂ)[X]) ^ 2) := by
            rw [degree_X_pow]; exact_mod_cast one_lt_two
  have hI : IsIntegral (integralClosure ℤ ℂ) x := by
    refine ⟨_, hmon, ?_⟩
    simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X, eval₂_C, eval₂_natCast]
    exact hx
  exact isIntegral_trans x hI

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
        ∃ β : 𝒪'', (q : 𝒪'') = χ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) * β ∧
          (IsUnit (χ' (CuspForm.heckeAlgebra.U hq hqN hqS₀)) ∨ ¬ IsUnit β)) := by
  classical
  have hS₀' : (↑S₀ : Set ℕ) ⊆ ↑S := Finset.coe_subset.mpr hS₀

  obtain ⟨p, hp, hp𝒪'⟩ := exists_prime_natCast_mem_maximalIdeal 𝒪'

  obtain ⟨M, _instM, hMN, f, hf, chig, hchig, iota, hiota⟩ :=
    CuspForm.exists_isNewform_point_factor N S hNS 𝒪' χ
  have hNS_M : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S := fun q hq hqM => hNS q hq (hqM.trans hMN)

  choose af haf using fun q : ℕ => CuspForm.forall_exists_qCoeff_eq_of_isNormalizedEigenform
    hf.isNormalizedEigenform q
  choose α₀ hα₀ using fun q : ℕ => exists_root_quadratic (qCoeff f q) (q : ℂ)
  have hα₀' : ∀ q : ℕ, α₀ q ^ 2 - (af q : ℂ) * α₀ q + q = 0 := fun q => by rw [haf]; exact hα₀ q
  set αI : ℕ → integralClosure ℤ ℂ := fun q => ⟨α₀ q, isIntegral_of_root (af q) q (α₀ q) (hα₀' q)⟩
    with hαIdef
  set βI : ℕ → integralClosure ℤ ℂ := fun q => af q - αI q with hβIdef
  have hαI_val : ∀ q, ((αI q : integralClosure ℤ ℂ) : ℂ) = α₀ q := fun q => rfl
  have hβI_val : ∀ q, ((βI q : integralClosure ℤ ℂ) : ℂ) = qCoeff f q - α₀ q := fun q => by
    simp only [hβIdef, hαIdef, AddSubgroupClass.coe_sub, haf]

  have hαI_root : ∀ q : ℕ, ((αI q : integralClosure ℤ ℂ) : ℂ) ^ 2 -
      qCoeff f q * ((αI q : integralClosure ℤ ℂ) : ℂ) + q = 0 := fun q => hα₀ q
  have hβI_root : ∀ q : ℕ, ((βI q : integralClosure ℤ ℂ) : ℂ) ^ 2 -
      qCoeff f q * ((βI q : integralClosure ℤ ℂ) : ℂ) + q = 0 := fun q => by
    rw [hβI_val]; linear_combination hα₀ q

  obtain ⟨χf, hχf⟩ := hf.isNormalizedEigenform.exists_ringHom_heckeAlgebra_integralClosure
    (CuspForm.hasIntegralStructure_two M) (↑S : Set ℕ)
  obtain ⟨χfℂ, hχfℂ, hχfℂT, -⟩ := hf.isNormalizedEigenform.exists_ringHom_heckeAlgebra (↑S : Set ℕ)
  have hχf_val : ∀ t, ((χf t : integralClosure ℤ ℂ) : ℂ) = χfℂ t := fun t =>
    smul_left_injective ℂ hf.ne_zero ((hχf t).symm.trans (hχfℂ t))

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

  set s₁ : Finset (integralClosure ℤ ℂ) :=
    N.primeFactors.image af ∪ N.primeFactors.image αI ∪ N.primeFactors.image βI with hs₁def
  set R₁ : Subalgebra ℤ (integralClosure ℤ ℂ) := R ⊔ Algebra.adjoin ℤ (↑s₁ : Set (integralClosure ℤ ℂ))
    with hR₁def
  obtain ⟨𝒪₁, _, _, _, _, _, _, _, _, _, hp𝒪₁, hinj₁, φ₁, hφ₁⟩ :=
    IntegralClosure.exists_extend_ringHom_dvr_finite hp𝒪' R s₁ φ
  have hs₁_sub : (↑s₁ : Set (integralClosure ℤ ℂ)) ⊆ R₁ := fun x hx =>
    (le_sup_right : Algebra.adjoin ℤ (↑s₁ : Set (integralClosure ℤ ℂ)) ≤ R₁) (Algebra.subset_adjoin hx)
  have hR_le_R₁ : R ≤ R₁ := le_sup_left
  have hpf : ∀ {q : ℕ}, q.Prime → q ∣ N → q ∈ N.primeFactors := fun hq hqN =>
    Nat.mem_primeFactors.mpr ⟨hq, hqN, NeZero.ne N⟩
  have haf_mem₁ : ∀ q : ℕ, q.Prime → q ∣ N → af q ∈ R₁ := fun q hq hqN =>
    hs₁_sub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (hpf hq hqN)))))
  have hαI_mem₁ : ∀ q : ℕ, q.Prime → q ∣ N → αI q ∈ R₁ := fun q hq hqN =>
    hs₁_sub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (hpf hq hqN)))))
  have hβI_mem₁ : ∀ q : ℕ, q.Prime → q ∣ N → βI q ∈ R₁ := fun q hq hqN =>
    hs₁_sub (Finset.mem_coe.mpr (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (hpf hq hqN))))

  let γI : ℕ → integralClosure ℤ ℂ := fun q =>
    if h : q.Prime ∧ q ∣ N then
      (if IsUnit (φ₁ ⟨αI q, hαI_mem₁ q h.1 h.2⟩) then αI q
        else if IsUnit (φ₁ ⟨βI q, hβI_mem₁ q h.1 h.2⟩) then βI q else αI q)
    else αI q
  have hγI_root : ∀ q : ℕ, ((γI q : integralClosure ℤ ℂ) : ℂ) ^ 2 -
      qCoeff f q * ((γI q : integralClosure ℤ ℂ) : ℂ) + q = 0 := by
    intro q
    simp only [γI]
    split_ifs
    · exact hαI_root q
    · exact hβI_root q
    · exact hαI_root q
    · exact hαI_root q
  have hγI_mem₁ : ∀ q : ℕ, q.Prime → q ∣ N → γI q ∈ R₁ := by
    intro q hq hqN
    simp only [γI, dif_pos (And.intro hq hqN)]
    split_ifs
    · exact hαI_mem₁ q hq hqN
    · exact hβI_mem₁ q hq hqN
    · exact hαI_mem₁ q hq hqN
  have hδI_mem₁ : ∀ q : ℕ, q.Prime → q ∣ N → af q - γI q ∈ R₁ := fun q hq hqN =>
    sub_mem (haf_mem₁ q hq hqN) (hγI_mem₁ q hq hqN)

  have hγI_pref : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
      IsUnit (φ₁ ⟨γI q, hγI_mem₁ q hq hqN⟩) ∨ ¬ IsUnit (φ₁ ⟨af q - γI q, hδI_mem₁ q hq hqN⟩) := by
    intro q hq hqN
    have hβeq : (⟨af q - αI q, sub_mem (haf_mem₁ q hq hqN) (hαI_mem₁ q hq hqN)⟩ : R₁) =
        ⟨βI q, hβI_mem₁ q hq hqN⟩ := Subtype.ext rfl
    have hαeq : (⟨af q - βI q, sub_mem (haf_mem₁ q hq hqN) (hβI_mem₁ q hq hqN)⟩ : R₁) =
        ⟨αI q, hαI_mem₁ q hq hqN⟩ := Subtype.ext (by simp [hβIdef])
    by_cases hA : IsUnit (φ₁ ⟨αI q, hαI_mem₁ q hq hqN⟩)
    · left
      have hγ : γI q = αI q := by simp only [γI, dif_pos (And.intro hq hqN), if_pos hA]
      have : (⟨γI q, hγI_mem₁ q hq hqN⟩ : R₁) = ⟨αI q, hαI_mem₁ q hq hqN⟩ := Subtype.ext hγ
      rw [this]; exact hA
    · by_cases hB : IsUnit (φ₁ ⟨βI q, hβI_mem₁ q hq hqN⟩)
      · left
        have hγ : γI q = βI q := by
          simp only [γI, dif_pos (And.intro hq hqN), if_neg hA, if_pos hB]
        have : (⟨γI q, hγI_mem₁ q hq hqN⟩ : R₁) = ⟨βI q, hβI_mem₁ q hq hqN⟩ := Subtype.ext hγ
        rw [this]; exact hB
      · right
        have hγ : γI q = αI q := by
          simp only [γI, dif_pos (And.intro hq hqN), if_neg hA, if_neg hB]
        have : (⟨af q - γI q, hδI_mem₁ q hq hqN⟩ : R₁) = ⟨βI q, hβI_mem₁ q hq hqN⟩ :=
          Subtype.ext (by simp only [hγ]; rfl)
        rw [this]; exact hB

  obtain ⟨g, hg, hgℓ, hg_eq, hg_root, hg_zero⟩ :=
    hf.isNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
      hMN (fun q => ((γI q : integralClosure ℤ ℂ) : ℂ)) (fun q _ _ _ _ => hγI_root q)
  obtain ⟨χg, hχg⟩ := hg.exists_ringHom_heckeAlgebra_integralClosure
    (CuspForm.hasIntegralStructure_two N) (↑S₀ : Set ℕ)
  obtain ⟨χgℂ, hχgℂ, hχgℂT, hχgℂU⟩ := hg.exists_ringHom_heckeAlgebra (↑S₀ : Set ℕ)
  have hχg_val : ∀ t, ((χg t : integralClosure ℤ ℂ) : ℂ) = χgℂ t := fun t =>
    smul_left_injective ℂ hg.ne_zero ((hχg t).symm.trans (hχgℂ t))

  haveI : Module.Finite ℤ (heckeAlgebra N 2 (↑S₀ : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two N (↑S₀ : Set ℕ)
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := ℤ) (M := heckeAlgebra N 2 (↑S₀ : Set ℕ))
  set s₂ : Finset (integralClosure ℤ ℂ) := G.image χg with hs₂def
  set R₂ : Subalgebra ℤ (integralClosure ℤ ℂ) := R₁ ⊔ Algebra.adjoin ℤ (↑s₂ : Set (integralClosure ℤ ℂ))
    with hR₂def
  obtain ⟨𝒪₂, _, _, _, _, _, _, _, _, _, -, hinj₂, φ₂, hφ₂⟩ :=
    IntegralClosure.exists_extend_ringHom_dvr_finite hp𝒪₁ R₁ s₂ φ₁
  have hs₂_sub : (↑s₂ : Set (integralClosure ℤ ℂ)) ⊆ R₂ := fun x hx =>
    (le_sup_right : Algebra.adjoin ℤ (↑s₂ : Set (integralClosure ℤ ℂ)) ≤ R₂) (Algebra.subset_adjoin hx)
  have hR₁_le_R₂ : R₁ ≤ R₂ := le_sup_left

  have hmem : ∀ t : heckeAlgebra N 2 (↑S₀ : Set ℕ), χg t ∈ R₂ := by
    intro t
    have ht : t ∈ Submodule.span ℤ (↑G : Set (heckeAlgebra N 2 (↑S₀ : Set ℕ))) := by
      rw [hG]; exact Submodule.mem_top
    induction ht using Submodule.span_induction with
    | mem x hx =>
      exact hs₂_sub (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul n x _ hx => rw [map_zsmul]; exact zsmul_mem hx n
  set χ' : heckeAlgebra N 2 (↑S₀ : Set ℕ) →+* 𝒪₂ := φ₂.comp (χg.codRestrict R₂ hmem) with hχ'def
  have hχ'_apply : ∀ t, χ' t = φ₂ ⟨χg t, hmem t⟩ := fun t => rfl

  have hφ₂_R₁ : ∀ (x : integralClosure ℤ ℂ) (hx₁ : x ∈ R₁) (hx₂ : x ∈ R₂),
      φ₂ ⟨x, hx₂⟩ = algebraMap 𝒪₁ 𝒪₂ (φ₁ ⟨x, hx₁⟩) := by
    intro x hx₁ hx₂
    rw [← hφ₂ ⟨x, hx₁⟩]
    rfl
  have hφ₁_R : ∀ (x : integralClosure ℤ ℂ) (hxR : x ∈ R) (hx₁ : x ∈ R₁),
      φ₁ ⟨x, hx₁⟩ = algebraMap 𝒪' 𝒪₁ (φ ⟨x, hxR⟩) := by
    intro x hxR hx₁
    rw [← hφ₁ ⟨x, hxR⟩]
    rfl

  letI instAlg : Algebra 𝒪' 𝒪₂ := ((algebraMap 𝒪₁ 𝒪₂).comp (algebraMap 𝒪' 𝒪₁)).toAlgebra
  have halg : algebraMap 𝒪' 𝒪₂ = (algebraMap 𝒪₁ 𝒪₂).comp (algebraMap 𝒪' 𝒪₁) := rfl
  haveI : IsScalarTower 𝒪' 𝒪₁ 𝒪₂ := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI instFin : Module.Finite 𝒪' 𝒪₂ := Module.Finite.trans 𝒪₁ 𝒪₂
  haveI instLoc : IsLocalHom (algebraMap 𝒪' 𝒪₂) := by
    rw [halg]; exact RingHom.isLocalHom_comp _ _
  have hinj : Function.Injective (algebraMap 𝒪' 𝒪₂) := by
    rw [halg]; exact hinj₂.comp hinj₁
  refine ⟨𝒪₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, instAlg, instFin, instLoc, hinj, χ', ?_, ?_, ?_⟩
  ·
    intro t
    have key : χ'.comp (Subalgebra.inclusion (heckeAlgebra_mono hS₀')).toRingHom =
        (algebraMap 𝒪' 𝒪₂).comp χ := by
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
      have hx₁ : χf (heckeAlgebra.T hℓ hℓM hℓS) ∈ R₁ := hR_le_R₁ hxR
      rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        hincl]
      change φ₂ ⟨χg (heckeAlgebra.T hℓ hℓN hℓS₀), hmem _⟩ = algebraMap 𝒪' 𝒪₂ (χ (heckeAlgebra.T hℓ hℓN hℓS))
      have h1 : (⟨χg (heckeAlgebra.T hℓ hℓN hℓS₀), hmem _⟩ : R₂) =
          ⟨χf (heckeAlgebra.T hℓ hℓM hℓS), hR₁_le_R₂ hx₁⟩ := Subtype.ext hval

      have hφχ : φ ⟨χf (heckeAlgebra.T hℓ hℓM hℓS), hxR⟩ = χ (heckeAlgebra.T hℓ hℓN hℓS) := by
        rw [← hiota ℓ hℓ hℓN hℓS, hφdef, RingHom.comp_apply]
        congr 1
        apply Subtype.ext
        change ((χf (heckeAlgebra.T hℓ hℓM hℓS) : integralClosure ℤ ℂ) : ℂ) = chig _
        rw [hχf_val, hchig_eq]
      rw [h1, hφ₂_R₁ _ hx₁, hφ₁_R _ hxR hx₁, halg, RingHom.comp_apply]
      change algebraMap 𝒪₁ 𝒪₂ (algebraMap 𝒪' 𝒪₁ (φ ⟨χf (heckeAlgebra.T hℓ hℓM hℓS), hxR⟩)) = _
      rw [hφχ]
      rfl
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
    have h1 : (⟨χg (heckeAlgebra.U hq hqN hqS₀), hmem _⟩ : R₂) = 0 := Subtype.ext hval0
    rw [h1, map_zero]
  ·
    intro q hq hqN hqS₀ hnsq

    set ev : R₂ →+* ℂ := (integralClosure ℤ ℂ).val.toRingHom.comp R₂.val.toRingHom with hevdef
    have hev_inj : Function.Injective ev := Subtype.val_injective.comp Subtype.val_injective
    have hev : ∀ y : R₂, ev y = ((y : integralClosure ℤ ℂ) : ℂ) := fun y => rfl
    set x : R₂ := ⟨χg (heckeAlgebra.U hq hqN hqS₀), hmem _⟩ with hxdef
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
      have hunit : IsUnit (φ₂ x) := by
        refine IsUnit.of_mul_eq_one (φ₂ x) ?_
        rw [← map_mul, ← sq, hsq1, map_one]
      refine ⟨φ₂ x * q, ?_, Or.inl hunit⟩
      rw [← mul_assoc, ← sq, ← map_pow, hsq1, map_one, one_mul]
    ·
      have hxeq : x = ⟨γI q, hR₁_le_R₂ (hγI_mem₁ q hq hqN)⟩ := hev_inj (by
        rw [hx, hev, hg_root q hq hqN hqM hnsq])
      set y : R₂ := ⟨af q - γI q, hR₁_le_R₂ (hδI_mem₁ q hq hqN)⟩ with hydef
      have hy : ev y = qCoeff f q - ((γI q : integralClosure ℤ ℂ) : ℂ) := by
        rw [hev, hydef]
        simp only [AddSubgroupClass.coe_sub, haf]
      have hprod : x * y = (q : R₂) := hev_inj (by
        rw [map_mul, map_natCast, hxeq, hev, hy]
        linear_combination (-1 : ℂ) * hγI_root q)
      refine ⟨φ₂ y, ?_, ?_⟩
      · rw [← map_mul, hprod, map_natCast]
      ·
        rw [hxeq, hφ₂_R₁ _ (hγI_mem₁ q hq hqN), hydef, hφ₂_R₁ _ (hδI_mem₁ q hq hqN),
          isUnit_map_iff (algebraMap 𝒪₁ 𝒪₂), isUnit_map_iff (algebraMap 𝒪₁ 𝒪₂)]
        exact hγI_pref q hq hqN

end K1EE1

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
        ∃ β : 𝒪'', (q : 𝒪'') = χ' (CuspForm.heckeAlgebra.U hq hqN hqS₀) * β ∧
          (IsUnit (χ' (CuspForm.heckeAlgebra.U hq hqN hqS₀)) ∨ ¬ IsUnit β)) :=
  K1EE1.main N S S₀ hS₀ hNS 𝒪' χ

end S_CuspForm_heckeAlgebra_exists_ringHom_extension_apply_U_eq_zero_and_isUnit_apply_U_or
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_ringHom_extension_apply_U_eq_zero_and_isUnit_apply_U_or (solution)

-- Prove2me | solution 1 for CuspForm.exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d178b184-e989-5c63-8cfb-1f46fff2676f

import Definitions.Def_CuspForm_NewLattice
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero
import Theorems.Thm_CuspForm_atkinLehnerLin_atkinLehnerLin
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_CuspForm_qCoeff_rescaleLin
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false

noncomputable section

namespace DeskWA_RATQ

open CongruenceSubgroup

private theorem exists_theta : ∃ θ : ℂ →ₗ[ℚ] ℂ,
    (∀ r : ℚ, θ (r : ℂ) = 0) ∧ (∀ z : ℂ, θ z = 0 → ∃ r : ℚ, z = (r : ℂ)) ∧
      ∀ (z : ℂ) (r : ℚ), θ (z * r) = θ z * r := by
  set ι : ℚ →ₗ[ℚ] ℂ := Algebra.linearMap ℚ ℂ with hι
  have hιapp : ∀ r : ℚ, ι r = (r : ℂ) := fun r => by simp [hι, Algebra.linearMap_apply]
  obtain ⟨π, hπ⟩ := ι.exists_leftInverse_of_injective
    ((LinearMap.ker_eq_bot (f := ι)).mpr fun x y hxy => by
      rw [hιapp, hιapp] at hxy
      exact_mod_cast hxy)
  have hπι : ∀ r : ℚ, π (r : ℂ) = r := fun r => by
    have h := LinearMap.congr_fun hπ r
    rw [LinearMap.comp_apply, LinearMap.id_apply, hιapp] at h
    exact h
  refine ⟨LinearMap.id - ι.comp π, fun r => ?_, fun z hz => ?_, fun z r => ?_⟩
  · rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hπι, hιapp, sub_self]
  · refine ⟨π z, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, sub_eq_zero, hιapp] at hz
    exact hz
  · have h1 : z * (r : ℂ) = r • z := by rw [Rat.smul_def, mul_comm]
    rw [h1, map_smul, Rat.smul_def, mul_comm]

private theorem one_mem_strictPeriods_gamma0 (N : ℕ) :
    (1 : ℝ) ∈ Subgroup.strictPeriods
      ((Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
        Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (Γ := Gamma0 N) ?_]
  · exact AddSubgroup.mem_zmultiples 1
  · refine Gamma0_mem.mpr ?_
    show ((ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 : ZMod N) = 0
    norm_num [ModularGroup.T]

variable {N : ℕ} {k : ℤ}

private def qCoeffL (N : ℕ) (k : ℤ) (n : ℕ) : CuspForm (Gamma0 N) k →ₗ[ℂ] ℂ where
  toFun φ := ModularFormClass.qCoeff (⇑φ) n
  map_add' φ ψ := by
    have hφ := ModularFormClass.analyticAt_cuspFunction_zero (f := φ) one_pos
      (one_mem_strictPeriods_gamma0 N)
    have hψ := ModularFormClass.analyticAt_cuspFunction_zero (f := ψ) one_pos
      (one_mem_strictPeriods_gamma0 N)
    simp only [ModularFormClass.qCoeff, CuspForm.coe_add]
    rw [UpperHalfPlane.qExpansion_add hφ hψ]
    simp
  map_smul' c φ := by
    have hφ := ModularFormClass.analyticAt_cuspFunction_zero (f := φ) one_pos
      (one_mem_strictPeriods_gamma0 N)
    have hcoe : ⇑(c • φ) = c • ⇑φ := rfl
    simp only [ModularFormClass.qCoeff]
    rw [hcoe, UpperHalfPlane.qExpansion_smul hφ c]
    simp

private theorem qCoeffL_apply (n : ℕ) (φ : CuspForm (Gamma0 N) k) :
    qCoeffL N k n φ = ModularFormClass.qCoeff (⇑φ) n := rfl

private theorem qCoeff_add (φ ψ : CuspForm (Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(φ + ψ)) n
      = ModularFormClass.qCoeff (⇑φ) n + ModularFormClass.qCoeff (⇑ψ) n :=
  map_add (qCoeffL N k n) φ ψ

private theorem qCoeff_sub (φ ψ : CuspForm (Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(φ - ψ)) n
      = ModularFormClass.qCoeff (⇑φ) n - ModularFormClass.qCoeff (⇑ψ) n :=
  map_sub (qCoeffL N k n) φ ψ

private theorem qCoeff_zero' (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (Gamma0 N) k)) n = 0 :=
  map_zero (qCoeffL N k n)

private theorem qCoeff_linearCombination {ι : Type*} (v : ι → CuspForm (Gamma0 N) k) (l : ι →₀ ℂ) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(Finsupp.linearCombination ℂ v l)) n
      = l.sum fun i a => a * ModularFormClass.qCoeff (⇑(v i)) n := by
  rw [← qCoeffL_apply, Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
  rfl

private theorem qCoeff_heckeULin [NeZero N] {q : ℕ} (hq : q ≠ 0) (hqN : q ∣ N)
    (φ : CuspForm (Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.heckeULin 2 hqN φ)) n
      = ModularFormClass.qCoeff (⇑φ) (n * q) := by
  rw [CuspForm.coe_heckeULin_apply,
    ModularFormClass.qCoeff_heckeU φ (one_mem_strictPeriods_gamma0 N) hq n]
  rfl

private theorem qCoeff_heckeTLin {q : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N)
    (φ : CuspForm (Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.heckeTLin 2 hq hqN φ)) n
      = ModularFormClass.qCoeff (⇑φ) (n * q)
        + if q ∣ n then (q : ℂ) ^ ((2 : ℤ) - 1) * ModularFormClass.qCoeff (⇑φ) (n / q) else 0 := by
  rw [CuspForm.coe_heckeTLin_apply,
    ModularFormClass.qCoeff_heckeT φ (one_mem_strictPeriods_gamma0 N) hq.ne_zero n]
  rfl

private theorem qCoeff_levelInclusionLin {R : ℕ} [NeZero N] (hRN : R ∣ N) (φ : CuspForm (Gamma0 R) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(FreyPackage.ModMCarrier.levelInclusionLin hRN 2 φ)) n
      = ModularFormClass.qCoeff (⇑φ) n := by
  rw [FreyPackage.ModMCarrier.coe_levelInclusionLin]

section Traces

variable {M q : ℕ} [NeZero M]

omit [NeZero M] in
private theorem dvd_level (A : ModularForm.AtkinLehnerDatum M q) : q ∣ M := ⟨A.R, A.hM⟩

omit [NeZero M] in
private theorem not_dvd_R (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) : ¬ q ∣ A.R := by
  intro h
  have hb := A.bezout
  have h1 : (q : ℤ) ∣ (q : ℤ) * A.a - (A.R : ℤ) * A.b :=
    dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h) _)
  rw [hb] at h1
  have : q = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1
  exact hq.one_lt.ne' this

private theorem neZero_R (A : ModularForm.AtkinLehnerDatum M q) : NeZero A.R :=
  ⟨fun h => NeZero.ne M (by rw [A.hM, h, mul_zero])⟩

private theorem levelInclusionLin_traceLin (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (Gamma0 M) 2) :
    FreyPackage.ModMCarrier.levelInclusionLin A.R_dvd 2 (CuspForm.traceLin A hq f)
      = f + CuspForm.heckeULin 2 (dvd_level A) (CuspForm.atkinLehnerLin A 2 f) := by
  refine DFunLike.ext' ?_
  rw [FreyPackage.ModMCarrier.coe_levelInclusionLin, CuspForm.coe_traceLin_apply, CuspForm.coe_add,
    CuspForm.coe_heckeULin_apply, CuspForm.coe_atkinLehnerLin_apply]

private theorem levelInclusionLin_traceLin_atkinLehnerLin (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (Gamma0 M) 2) :
    FreyPackage.ModMCarrier.levelInclusionLin A.R_dvd 2
        (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))
      = CuspForm.atkinLehnerLin A 2 f + CuspForm.heckeULin 2 (dvd_level A) f := by
  refine DFunLike.ext' ?_
  rw [FreyPackage.ModMCarrier.coe_levelInclusionLin, CuspForm.coe_traceLin_apply, CuspForm.coe_add,
    CuspForm.coe_heckeULin_apply, ← CuspForm.coe_atkinLehnerLin_apply A 2,
    CuspForm.atkinLehnerLin_atkinLehnerLin]

private theorem qCoeff_traceLin (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (Gamma0 M) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.traceLin A hq f)) n
      = ModularFormClass.qCoeff (⇑f) n
        + ModularFormClass.qCoeff (⇑(CuspForm.atkinLehnerLin A 2 f)) (n * q) := by
  have h := congrArg (fun φ : CuspForm (Gamma0 M) 2 => ModularFormClass.qCoeff (⇑φ) n)
    (levelInclusionLin_traceLin A hq f)
  rw [qCoeff_levelInclusionLin] at h
  rw [h, qCoeff_add, qCoeff_heckeULin hq.ne_zero]

private theorem qCoeff_traceLin_atkinLehnerLin (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (Gamma0 M) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))) n
      = ModularFormClass.qCoeff (⇑(CuspForm.atkinLehnerLin A 2 f)) n
        + ModularFormClass.qCoeff (⇑f) (n * q) := by
  have h := congrArg (fun φ : CuspForm (Gamma0 M) 2 => ModularFormClass.qCoeff (⇑φ) n)
    (levelInclusionLin_traceLin_atkinLehnerLin A hq f)
  rw [qCoeff_levelInclusionLin] at h
  rw [h, qCoeff_add, qCoeff_heckeULin hq.ne_zero]

private theorem key (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) (f : CuspForm (Gamma0 M) 2) :
    FreyPackage.ModMCarrier.rescaleLin A.q_mul_R_dvd 2
        (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))
      = (f - CuspForm.heckeULin 2 (dvd_level A) (CuspForm.heckeULin 2 (dvd_level A) f))
        + FreyPackage.ModMCarrier.levelInclusionLin A.R_dvd 2
          (CuspForm.heckeTLin 2 hq (not_dvd_R A hq)
              (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))
            - CuspForm.traceLin A hq f) := by
  refine ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_gamma0 M) fun n => ?_
  rw [CuspForm.qCoeff_rescaleLin, qCoeff_add, qCoeff_sub, qCoeff_levelInclusionLin, qCoeff_sub,
    qCoeff_heckeTLin, qCoeff_heckeULin hq.ne_zero, qCoeff_heckeULin hq.ne_zero,
    qCoeff_traceLin_atkinLehnerLin A hq f (n * q), qCoeff_traceLin A hq f n]
  split_ifs <;> ring

end Traces

section Descent

private theorem theta_finsuppSum (θ : ℂ →ₗ[ℚ] ℂ) (hθ : ∀ (z : ℂ) (r : ℚ), θ (z * r) = θ z * r)
    {ι : Type*} (l : ι →₀ ℂ) (w : ι → ℂ) (hw : ∀ i, ∃ r : ℚ, w i = (r : ℂ)) :
    θ (l.sum fun i a => a * w i) = (Finsupp.mapRange θ (map_zero θ) l).sum fun i a => a * w i := by
  rw [Finsupp.sum_mapRange_index (fun i => by simp)]
  unfold Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨r, hr⟩ := hw i
  show θ (l i * w i) = θ (l i) * w i
  rw [hr, hθ]

end Descent

section Assembly

variable {M q : ℕ} [NeZero M]

private theorem main (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) (f : CuspForm (Gamma0 M) 2)
    (hf : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)) (n : ℕ) :
    (∃ r : ℚ, ModularFormClass.qCoeff (⇑(CuspForm.traceLin A hq f)) n = (r : ℂ)) ∧
    (∃ r : ℚ, ModularFormClass.qCoeff
      (⇑(CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))) n = (r : ℂ)) := by
  haveI := neZero_R A
  obtain ⟨θ, hθrat, hθker, hθmul⟩ := exists_theta
  have hθint : ∀ m : ℤ, θ (m : ℂ) = 0 := fun m => by exact_mod_cast hθrat m
  have hθf : ∀ m : ℕ, θ (ModularFormClass.qCoeff (⇑f) m) = 0 := fun m => by
    obtain ⟨z, hz⟩ := hf m
    rw [hz]
    exact hθint z
  have hθite : ∀ (P : Prop) [Decidable P] (S : ℂ),
      θ (if P then (q : ℂ) ^ ((2 : ℤ) - 1) * S else 0)
        = if P then (q : ℂ) ^ ((2 : ℤ) - 1) * θ S else 0 := by
    intro P _ S
    split_ifs
    · have hcast : (q : ℂ) ^ ((2 : ℤ) - 1) = ((q : ℚ) : ℂ) := by norm_num
      rw [hcast, mul_comm, hθmul, mul_comm]
    · exact map_zero θ

  set Gen : Set (CuspForm (Gamma0 A.R) 2) :=
    {h | ∀ m : ℕ, ∃ z : ℤ, ModularFormClass.qCoeff h m = (z : ℂ)} with hGen
  have hspanGen : Submodule.span ℂ Gen = ⊤ := by
    have h := CuspForm.hasIntegralStructure_two A.R
    unfold CuspForm.HasIntegralStructure CuspForm.intLattice at h
    rwa [Submodule.span_span_of_tower] at h
  obtain ⟨b, hbGen, hbspan, hli⟩ := exists_linearIndependent ℂ Gen
  have hbtop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → CuspForm (Gamma0 A.R) 2)) := by
    rw [Subtype.range_coe, hbspan, hspanGen]
  set B : Module.Basis b ℂ (CuspForm (Gamma0 A.R) 2) := Module.Basis.mk hli hbtop with hB
  have hbcoeff : ∀ (x : b) (m : ℕ), ∃ r : ℚ,
      ModularFormClass.qCoeff (⇑(B x)) m = (r : ℂ) := fun x m => by
    obtain ⟨z, hz⟩ := hbGen x.2 m
    refine ⟨z, ?_⟩
    rw [hB, Module.Basis.mk_apply]
    exact_mod_cast hz

  set β : b →₀ ℂ := B.repr (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f)) with hβ
  set α : b →₀ ℂ := B.repr (CuspForm.traceLin A hq f
    - CuspForm.heckeTLin 2 hq (not_dvd_R A hq)
        (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))) with hα
  have ht₂eq : Finsupp.linearCombination ℂ B β
      = CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f) := B.linearCombination_repr _
  have hseq : Finsupp.linearCombination ℂ B α
      = CuspForm.traceLin A hq f
        - CuspForm.heckeTLin 2 hq (not_dvd_R A hq)
            (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f)) := B.linearCombination_repr _
  set β' : b →₀ ℂ := Finsupp.mapRange θ (map_zero θ) β with hβ'
  set α' : b →₀ ℂ := Finsupp.mapRange θ (map_zero θ) α with hα'

  have hF : f - CuspForm.heckeULin 2 (dvd_level A) (CuspForm.heckeULin 2 (dvd_level A) f)
      = FreyPackage.ModMCarrier.rescaleLin A.q_mul_R_dvd 2
          (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))
        + FreyPackage.ModMCarrier.levelInclusionLin A.R_dvd 2
          (CuspForm.traceLin A hq f
            - CuspForm.heckeTLin 2 hq (not_dvd_R A hq)
                (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))) := by
    rw [key A hq f, add_assoc, ← map_add, sub_add_sub_cancel, sub_self, map_zero, add_zero]
  have hFcoeff : ∀ m : ℕ, θ (ModularFormClass.qCoeff
      (⇑(FreyPackage.ModMCarrier.rescaleLin A.q_mul_R_dvd 2
          (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))
        + FreyPackage.ModMCarrier.levelInclusionLin A.R_dvd 2
          (CuspForm.traceLin A hq f
            - CuspForm.heckeTLin 2 hq (not_dvd_R A hq)
                (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))))) m) = 0 := fun m => by
    rw [← hF, qCoeff_sub, qCoeff_heckeULin hq.ne_zero, qCoeff_heckeULin hq.ne_zero, map_sub,
      hθf, hθf, sub_zero]

  set u : CuspForm (Gamma0 A.R) 2 := Finsupp.linearCombination ℂ B β' with hu
  set v : CuspForm (Gamma0 A.R) 2 := Finsupp.linearCombination ℂ B α' with hv
  have hGcoeff : ∀ m : ℕ, ModularFormClass.qCoeff
      (⇑(FreyPackage.ModMCarrier.levelInclusionLin A.R_dvd 2 v
        + FreyPackage.ModMCarrier.rescaleLin A.q_mul_R_dvd 2 u)) m = 0 := fun m => by
    have h0 := hFcoeff m
    rw [qCoeff_add, CuspForm.qCoeff_rescaleLin, qCoeff_levelInclusionLin, ← hseq, ← ht₂eq,
      qCoeff_linearCombination, qCoeff_linearCombination, map_add, hθite,
      theta_finsuppSum θ hθmul β _ (fun x => hbcoeff x (m / q)),
      theta_finsuppSum θ hθmul α _ (fun x => hbcoeff x m), ← hβ', ← hα'] at h0
    rw [qCoeff_add, CuspForm.qCoeff_rescaleLin, qCoeff_levelInclusionLin, hu, hv,
      qCoeff_linearCombination, qCoeff_linearCombination]
    rw [add_comm]
    exact h0
  have hG : FreyPackage.ModMCarrier.levelInclusionLin A.R_dvd 2 v
      + FreyPackage.ModMCarrier.rescaleLin A.q_mul_R_dvd 2 u = 0 :=
    ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_gamma0 M) fun m => by
      rw [hGcoeff]
      exact (qCoeff_zero' (N := M) (k := 2) m).symm

  have huv := FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero hq (not_dvd_R A hq)
    A.R_dvd A.q_mul_R_dvd v u hG
  have hβ'0 : β' = 0 :=
    linearIndependent_iff.mp B.linearIndependent β' (by rw [← hu]; exact huv.2)

  have ht₂rat : ∀ m : ℕ, θ (ModularFormClass.qCoeff
      (⇑(CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))) m) = 0 := fun m => by
    rw [← ht₂eq, qCoeff_linearCombination, theta_finsuppSum θ hθmul β _ (fun x => hbcoeff x m),
      ← hβ', hβ'0, Finsupp.sum_zero_index]

  have hgn : θ (ModularFormClass.qCoeff (⇑(CuspForm.atkinLehnerLin A 2 f)) (n * q)) = 0 := by
    have h := ht₂rat (n * q)
    rwa [qCoeff_traceLin_atkinLehnerLin A hq f, map_add, hθf, add_zero] at h
  refine ⟨hθker _ ?_, hθker _ (ht₂rat n)⟩
  rw [qCoeff_traceLin A hq f n, map_add, hθf, zero_add]
  exact hgn

end Assembly

end DeskWA_RATQ

theorem solution
    {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (hf : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)) (n : ℕ) :
    (∃ r : ℚ, ModularFormClass.qCoeff (⇑(CuspForm.traceLin A hq f)) n = (r : ℂ)) ∧
    (∃ r : ℚ, ModularFormClass.qCoeff
      (⇑(CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f))) n = (r : ℂ)) :=
  DeskWA_RATQ.main A hq f hf n

end

end S_CuspForm_exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff
end P2MW
export P2MW.S_CuspForm_exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff (solution)

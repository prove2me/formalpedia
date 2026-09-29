-- Prove2me | solution 1 for CuspForm.apply_eq_zero_of_traceLin_eq_zero_of_forall_mem_newLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fc1a7e44-f8c3-5aea-8764-3bdfe51ca6b4

import Definitions.Def_CuspForm_NewLattice
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
import Theorems.Thm_CuspForm_traceLin_heckeTLin
import Theorems.Thm_ModularForm_alSlash_heckeT_comm
import Theorems.Thm_CuspForm_mem_intLattice_of_coe_eq_heckeT
import Theorems.Thm_CuspForm_mem_intLattice_of_coe_eq_heckeU
import Theorems.Thm_CuspForm_exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_apply_eq_zero_of_traceLin_eq_zero_of_forall_mem_newLattice
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
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false
set_option Elab.async false
open CongruenceSubgroup

namespace INHRATS

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [DecidableEq V]

theorem span_insert_shear (t : Finset V) (x₀ : V) (a : V → ℂ) (ha : ∀ x ∈ t, a x ≠ 0)
    (b : V → ℂ) :
    Submodule.span ℂ (insert x₀ ↑(t.image fun x => a x • x - b x • x₀) : Set V)
      = Submodule.span ℂ (insert x₀ (t : Set V)) := by
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · obtain ⟨x, hx, rfl⟩ := hy
      refine sub_mem (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ hx)
      · exact Submodule.subset_span (Set.mem_insert _ _)
  · rw [Submodule.span_le]
    rintro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · have h1 : a y • y - b y • x₀ ∈ Submodule.span ℂ
          (insert x₀ ((fun x => a x • x - b x • x₀) '' ↑t) : Set V) :=
        Submodule.subset_span (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩)
      have h0 : x₀ ∈ Submodule.span ℂ
          (insert x₀ ((fun x => a x • x - b x • x₀) '' ↑t) : Set V) :=
        Submodule.subset_span (Set.mem_insert _ _)
      have hay : a y • y ∈ Submodule.span ℂ
          (insert x₀ ((fun x => a x • x - b x • x₀) '' ↑t) : Set V) := by
        have := add_mem h1 (Submodule.smul_mem _ (b y) h0)
        simpa [sub_add_cancel] using this
      have := Submodule.smul_mem _ (a y)⁻¹ hay
      simpa [smul_smul, inv_mul_cancel₀ (ha y hy)] using this

theorem mem_span_ker_of_mem_span_finset {ι : Type*} (Φ : ι → V →ₗ[ℂ] ℂ) (t : Finset V)
    (hrat : ∀ x ∈ t, ∀ i, Φ i x ∈ (algebraMap ℚ ℂ).range)
    (f : V) (hf : f ∈ Submodule.span ℂ (t : Set V)) (hker : ∀ i, Φ i f = 0) :
    f ∈ Submodule.span ℂ
      {x : V | x ∈ Submodule.span ℤ (t : Set V) ∧ ∀ i, Φ i x = 0} := by
  classical
  induction ht : t.card using Nat.strong_induction_on generalizing t f with
  | _ n ih =>
  subst ht
  by_cases hclean : ∀ x ∈ t, ∀ i, Φ i x = 0
  · refine Submodule.span_mono ?_ (by exact hf : f ∈ Submodule.span ℂ (t : Set V))
    exact fun x hx => ⟨Submodule.subset_span hx, fun i => hclean x hx i⟩
  · push Not at hclean
    obtain ⟨x₀, hx₀t, i₀, hi₀⟩ := hclean

    have hwit : ∀ x ∈ t, ∃ r : ℚ, (r : ℂ) = Φ i₀ x := by
      intro x hx
      obtain ⟨r, hr⟩ := hrat x hx i₀
      exact ⟨r, by simpa using hr⟩
    set rf : V → ℚ := fun x => if hx : x ∈ t then (hwit x hx).choose else 0 with hrf
    have hrf_eq : ∀ x ∈ t, ((rf x : ℚ) : ℂ) = Φ i₀ x := by
      intro x hx
      simp only [hrf, dif_pos hx]
      exact (hwit x hx).choose_spec
    have hrx₀ : rf x₀ ≠ 0 := by
      intro h0
      apply hi₀
      rw [← hrf_eq x₀ hx₀t, h0]
      simp

    set a : V → ℂ := fun x => ((rf x₀).num : ℂ) * ((rf x).den : ℂ) with ha_def
    set b : V → ℂ := fun x => ((rf x).num : ℂ) * ((rf x₀).den : ℂ) with hb_def
    have ha_ne : ∀ x ∈ t, a x ≠ 0 := by
      intro x hx
      simp only [ha_def]
      exact mul_ne_zero (Int.cast_ne_zero.mpr (Rat.num_ne_zero.mpr hrx₀))
        (Nat.cast_ne_zero.mpr (rf x).den_nz)
    set t' : Finset V := (t.erase x₀).image (fun x => a x • x - b x • x₀) with ht'

    have hkill : ∀ y ∈ t', Φ i₀ y = 0 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hxt := Finset.mem_of_mem_erase hx
      have hdx : (((rf x).den : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (rf x).den_nz
      have hdx₀ : (((rf x₀).den : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (rf x₀).den_nz
      have hx_val : Φ i₀ x = ((rf x).num : ℂ) / ((rf x).den : ℂ) := by
        rw [← hrf_eq x hxt, Rat.cast_def]
      have hx₀_val : Φ i₀ x₀ = ((rf x₀).num : ℂ) / ((rf x₀).den : ℂ) := by
        rw [← hrf_eq x₀ hx₀t, Rat.cast_def]
      simp only [map_sub, map_smul, smul_eq_mul, ha_def, hb_def, hx_val, hx₀_val]
      field_simp
      ring

    have hratt' : ∀ y ∈ t', ∀ i, Φ i y ∈ (algebraMap ℚ ℂ).range := by
      intro y hy i
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hxt := Finset.mem_of_mem_erase hx
      simp only [map_sub, map_smul, smul_eq_mul]
      refine sub_mem (mul_mem ?_ (hrat x hxt i)) (mul_mem ?_ (hrat x₀ hx₀t i))
      · simp only [ha_def]
        exact mul_mem ⟨((rf x₀).num : ℚ), by simp [map_intCast]⟩
          ⟨((rf x).den : ℚ), by simp [map_natCast]⟩
      · simp only [hb_def]
        exact mul_mem ⟨((rf x).num : ℚ), by simp [map_intCast]⟩
          ⟨((rf x₀).den : ℚ), by simp [map_natCast]⟩

    have hspan_eq : Submodule.span ℂ (t : Set V)
        = Submodule.span ℂ (insert x₀ (t' : Set V)) := by
      conv_lhs => rw [← Finset.insert_erase hx₀t]
      rw [Finset.coe_insert,
        ← span_insert_shear (t.erase x₀) x₀ a (fun x hx => ha_ne x (Finset.mem_of_mem_erase hx)) b,
        ht']

    rw [hspan_eq] at hf
    obtain ⟨α, g, hg, rfl⟩ := Submodule.mem_span_insert.mp hf

    have hg_kill : Φ i₀ g = 0 := by
      have hle : Submodule.span ℂ (t' : Set V) ≤ LinearMap.ker (Φ i₀) := by
        rw [Submodule.span_le]
        exact fun y hy => LinearMap.mem_ker.mpr (hkill y hy)
      exact LinearMap.mem_ker.mp (hle hg)

    have hα : α = 0 := by
      have h0 := hker i₀
      simp only [map_add, map_smul, smul_eq_mul, hg_kill, add_zero] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hi₀
    rw [hα, zero_smul, zero_add]

    have hcard : t'.card < t.card := by
      calc t'.card ≤ (t.erase x₀).card := Finset.card_image_le
        _ < t.card := Finset.card_erase_lt_of_mem hx₀t
    have hrec := ih t'.card hcard t' hratt' g hg
      (fun i => by
        have h0 := hker i
        simp only [map_add, map_smul, smul_eq_mul, hα, zero_mul, zero_add] at h0
        exact h0) rfl

    refine Submodule.span_mono ?_ hrec
    rintro y ⟨hyZ, hyK⟩
    refine ⟨?_, hyK⟩
    have ht'Z : (t' : Set V) ⊆ (Submodule.span ℤ (t : Set V) : Set V) := by
      rintro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hz)
      have hxt := Finset.mem_of_mem_erase hx
      have hac : a x = (((rf x₀).num * ((rf x).den : ℤ) : ℤ) : ℂ) := by
        simp only [ha_def]; push_cast; ring
      have hbc : b x = (((rf x).num * ((rf x₀).den : ℤ) : ℤ) : ℂ) := by
        simp only [hb_def]; push_cast; ring
      have hax : a x • x = ((rf x₀).num * ((rf x).den : ℤ)) • x := by
        rw [hac, Int.cast_smul_eq_zsmul]
      have hbx : b x • x₀ = ((rf x).num * ((rf x₀).den : ℤ)) • x₀ := by
        rw [hbc, Int.cast_smul_eq_zsmul]
      rw [hax, hbx]
      exact sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span hxt))
        (Submodule.smul_mem _ _ (Submodule.subset_span hx₀t))
    have : Submodule.span ℤ (t' : Set V) ≤ Submodule.span ℤ (t : Set V) :=
      Submodule.span_le.mpr ht'Z
    exact this hyZ

theorem mem_span_ker_of_span_eq_top {ι : Type*} (Φ : ι → V →ₗ[ℂ] ℂ) (S : Set V)
    (hspan : Submodule.span ℂ S = ⊤)
    (hrat : ∀ x ∈ S, ∀ i, Φ i x ∈ (algebraMap ℚ ℂ).range)
    (f : V) (hker : ∀ i, Φ i f = 0) :
    f ∈ Submodule.span ℂ {x : V | x ∈ Submodule.span ℤ S ∧ ∀ i, Φ i x = 0} := by
  have hf : f ∈ Submodule.span ℂ S := hspan ▸ Submodule.mem_top
  obtain ⟨t, hts, hft⟩ := Submodule.mem_span_finite_of_mem_span hf
  have hrec := mem_span_ker_of_mem_span_finset Φ t
    (fun x hx i => hrat x (hts hx) i) f hft hker
  refine Submodule.span_mono ?_ hrec
  rintro y ⟨hyZ, hyK⟩
  exact ⟨Submodule.span_mono hts hyZ, hyK⟩

variable {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)

theorem atkinLehnerLin_heckeTLin_comm {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f : CuspForm (Gamma0 M) 2) :
    CuspForm.atkinLehnerLin A 2 (CuspForm.heckeTLin 2 hℓ hℓM f)
      = CuspForm.heckeTLin 2 hℓ hℓM (CuspForm.atkinLehnerLin A 2 f) := by
  ext τ
  have h := ModularForm.alSlash_heckeT_comm A 2 hℓ hℓM
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)
  calc (CuspForm.atkinLehnerLin A 2 (CuspForm.heckeTLin 2 hℓ hℓM f)) τ
      = ModularForm.alSlash A 2 (ModularForm.heckeT 2 ℓ ⇑f) τ := by
        simp [CuspForm.coe_atkinLehnerLin_apply, CuspForm.coe_heckeTLin_apply]
    _ = ModularForm.heckeT 2 ℓ (ModularForm.alSlash A 2 ⇑f) τ := by rw [h]
    _ = (CuspForm.heckeTLin 2 hℓ hℓM (CuspForm.atkinLehnerLin A 2 f)) τ := by
        simp [CuspForm.coe_atkinLehnerLin_apply, CuspForm.coe_heckeTLin_apply]

theorem apply_triple_of_mem_heckeAlgebra
    (t : Module.End ℂ (CuspForm (Gamma0 M) 2))
    (ht : t ∈ CuspForm.heckeAlgebra M 2 {ℓ : ℕ | ℓ ∣ M}) :
    ∀ g : CuspForm (Gamma0 M) 2, g ∈ CuspForm.intLattice M 2 →
      CuspForm.traceLin A hq g = 0 →
      CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 g) = 0 →
      t g ∈ CuspForm.intLattice M 2 ∧ CuspForm.traceLin A hq (t g) = 0 ∧
        CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 (t g)) = 0 := by
  have ht' : t ∈ Algebra.adjoin ℤ (CuspForm.heckeGenerators M 2 {ℓ : ℕ | ℓ ∣ M}) := ht
  clear ht
  induction ht' using Algebra.adjoin_induction with
  | mem x hx =>
      intro g hgL hg0 hg1
      rcases hx with ⟨ℓ, hℓ, hℓM, hℓS, rfl⟩ | ⟨q', hq'M, hq'p, hq'S, rfl⟩
      · have hℓR : ¬ ℓ ∣ A.R := fun hdvd => hℓM (by rw [A.hM]; exact hdvd.mul_left q)
        refine ⟨?_, ?_, ?_⟩
        · exact CuspForm.mem_intLattice_of_coe_eq_heckeT (by norm_num) hℓ.ne_zero
            (CuspForm.coe_heckeTLin_apply 2 hℓ hℓM g) hgL
        · rw [show (CuspForm.heckeTLin 2 hℓ hℓM : Module.End ℂ _) g
              = CuspForm.heckeTLin 2 hℓ hℓM g from rfl,
            CuspForm.traceLin_heckeTLin A hq hℓ hℓM hℓR g, hg0, map_zero]
        · rw [show (CuspForm.heckeTLin 2 hℓ hℓM : Module.End ℂ _) g
              = CuspForm.heckeTLin 2 hℓ hℓM g from rfl,
            atkinLehnerLin_heckeTLin_comm A hℓ hℓM g,
            CuspForm.traceLin_heckeTLin A hq hℓ hℓM hℓR (CuspForm.atkinLehnerLin A 2 g),
            hg1, map_zero]
      · exact absurd hq'M hq'S
  | algebraMap r =>
      intro g hgL hg0 hg1
      have happ : (algebraMap ℤ (Module.End ℂ (CuspForm (Gamma0 M) 2)) r) g = r • g := by
        rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      refine ⟨?_, ?_, ?_⟩
      · rw [happ]; exact Submodule.smul_mem _ r hgL
      · rw [happ, map_zsmul, hg0, smul_zero]
      · rw [happ, map_zsmul, map_zsmul, hg1, smul_zero]
  | add x y hx hy ihx ihy =>
      intro g hgL hg0 hg1
      obtain ⟨hx1, hx2, hx3⟩ := ihx g hgL hg0 hg1
      obtain ⟨hy1, hy2, hy3⟩ := ihy g hgL hg0 hg1
      refine ⟨?_, ?_, ?_⟩
      · exact add_mem hx1 hy1
      · rw [LinearMap.add_apply, map_add, hx2, hy2, add_zero]
      · rw [LinearMap.add_apply, map_add, map_add, hx3, hy3, add_zero]
  | mul x y hx hy ihx ihy =>
      intro g hgL hg0 hg1
      obtain ⟨hy1, hy2, hy3⟩ := ihy g hgL hg0 hg1
      have := ihx (y g) hy1 hy2 hy3
      simpa [Module.End.mul_apply] using this

theorem mem_newLattice_of_mem_intLattice_of_traceLin_eq_zero
    (f : CuspForm (Gamma0 M) 2) (hfL : f ∈ CuspForm.intLattice M 2)
    (h₀ : CuspForm.traceLin A hq f = 0)
    (h₁ : CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f) = 0) :
    f ∈ CuspForm.newLattice A hq :=
  fun t ht => apply_triple_of_mem_heckeAlgebra A hq t ht f hfL h₀ h₁

theorem one_mem_strictPeriods_gamma0 (M : ℕ) :
    (1 : ℝ) ∈ Subgroup.strictPeriods
      ((Gamma0 M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
        Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (Γ := Gamma0 M) ?_]
  · exact AddSubgroup.mem_zmultiples 1
  · refine Gamma0_mem.mpr ?_
    show ((ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0 : ZMod M) = 0
    norm_num [ModularGroup.T]

variable {M : ℕ} [NeZero M]

noncomputable def qCoeffL (k : ℤ) (n : ℕ) : CuspForm (Gamma0 M) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := by
    have hf := ModularFormClass.analyticAt_cuspFunction_zero (f := f) one_pos
      (one_mem_strictPeriods_gamma0 M)
    have hg := ModularFormClass.analyticAt_cuspFunction_zero (f := g) one_pos
      (one_mem_strictPeriods_gamma0 M)
    simp only [ModularFormClass.qCoeff, CuspForm.coe_add]
    rw [UpperHalfPlane.qExpansion_add hf hg]
    simp
  map_smul' c f := by
    have hf := ModularFormClass.analyticAt_cuspFunction_zero (f := f) one_pos
      (one_mem_strictPeriods_gamma0 M)
    have hcoe : ⇑(c • f) = c • ⇑f := rfl
    simp only [ModularFormClass.qCoeff]
    rw [hcoe, UpperHalfPlane.qExpansion_smul hf c]
    simp

variable {q : ℕ} (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)

noncomputable def Phi [NeZero A.R] : ℕ ⊕ ℕ → (CuspForm (Gamma0 M) 2 →ₗ[ℂ] ℂ)
  | .inl n => (qCoeffL (M := A.R) 2 n).comp (CuspForm.traceLin A hq)
  | .inr n => (qCoeffL (M := A.R) 2 n).comp
      ((CuspForm.traceLin A hq).comp (CuspForm.atkinLehnerLin A 2))

end INHRATS

theorem solution
    {M q : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime)
    (t : CuspForm.heckeAlgebra M 2 {ℓ | ℓ ∣ M})
    (ht : ∀ g ∈ CuspForm.newLattice A hq,
      (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) g = 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (h₀ : CuspForm.traceLin A hq f = 0)
    (h₁ : CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f) = 0) :
    (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) f = 0 := by
  classical
  haveI hR : NeZero A.R := ⟨fun h => (NeZero.ne M) (by rw [A.hM, h, mul_zero])⟩
  set S : Set (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
    {g | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑g) n = (m : ℂ)} with hS
  have hLS : CuspForm.intLattice M 2 = Submodule.span ℤ S := rfl
  have hspan : Submodule.span ℂ S = ⊤ := by
    have h0 : Submodule.span ℂ
        ((CuspForm.intLattice M 2 :
          Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) :
            Set (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) = ⊤ :=
      CuspForm.hasIntegralStructure_two M
    rw [hLS] at h0
    rw [← Submodule.span_span_of_tower ℤ ℂ S]
    exact h0
  have hrat : ∀ x ∈ S, ∀ i, INHRATS.Phi A hq i x ∈ (algebraMap ℚ ℂ).range := by
    intro x hx i
    obtain ⟨⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩⟩ :=
      CuspForm.exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff A hq x hx
        (match i with | .inl n => n | .inr n => n)
    cases i with
    | inl n => exact ⟨r₀, by rw [eq_ratCast]; exact hr₀.symm⟩
    | inr n => exact ⟨r₁, by rw [eq_ratCast]; exact hr₁.symm⟩
  have hker : ∀ i, INHRATS.Phi A hq i f = 0 := by
    rintro (n | n)
    · show INHRATS.qCoeffL 2 n (CuspForm.traceLin A hq f) = 0
      rw [h₀, map_zero]
    · show INHRATS.qCoeffL 2 n (CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f)) = 0
      rw [h₁, map_zero]
  have hdes := INHRATS.mem_span_ker_of_span_eq_top (INHRATS.Phi A hq) S hspan hrat f hker
  have hkill : Submodule.span ℂ
      {x | x ∈ Submodule.span ℤ S ∧ ∀ i, INHRATS.Phi A hq i x = 0}
      ≤ LinearMap.ker (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) := by
    rw [Submodule.span_le]
    rintro x ⟨hxZ, hxK⟩
    refine LinearMap.mem_ker.mpr (ht x ?_)
    have hxL : x ∈ CuspForm.intLattice M 2 := hLS ▸ hxZ
    obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (A.R + 1)
    have hpR : ¬ p ∣ A.R := fun hdvd =>
      absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne A.R)) hdvd) (by omega)
    have h0x : CuspForm.traceLin A hq x = 0 :=
      CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero hpp hpR _
        (fun n _ => hxK (.inl n))
    have h1x : CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 x) = 0 :=
      CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero hpp hpR _
        (fun n _ => hxK (.inr n))
    exact INHRATS.mem_newLattice_of_mem_intLattice_of_traceLin_eq_zero A hq x hxL h0x h1x
  exact LinearMap.mem_ker.mp (hkill hdes)

end S_CuspForm_apply_eq_zero_of_traceLin_eq_zero_of_forall_mem_newLattice
end P2MW
export P2MW.S_CuspForm_apply_eq_zero_of_traceLin_eq_zero_of_forall_mem_newLattice (solution)

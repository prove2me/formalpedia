-- Prove2me | solution 1 for CohCarrier.eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/42f2685f-b545-5b72-820b-a914ad3b3f31

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodHomPair
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice
import Theorems.Thm_ModularCurve_periodMap_rescaleLin_apply
import Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_top
import Theorems.Thm_ModularCurve_existsPeriodMapLinear
import Theorems.Thm_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero
import Theorems.Thm_FreyPackage_ModMCarrier_rescaleLin_eq_levelInclusionLin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule Ihara.wConj_coe Ihara.wConj_symm_coe"
p2m_attr_erase "simp" "Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped MatrixGroups
open CongruenceSubgroup CohCarrier ModularCurve ModularCurve.Period

namespace OldInj

theorem jConjSL_mem_GammaH_top {L : ℕ} (γ : ↥(GammaH L ⊤)) : jConjSL (γ : SL(2, ℤ)) ∈ GammaH L ⊤ := by
  have hmem : jConjSL (γ : SL(2, ℤ)) ∈ Gamma0 L := jConjSL_mem_Gamma0 (GammaH_le_Gamma0 ⊤ γ.2)
  rw [mem_GammaH_iff]
  exact ⟨hmem, Subgroup.mem_top _⟩

theorem iotaDeg_jConj {R M d : ℕ} [NeZero d] (h : LevelLE R M ⊤ ⊤ d) (γ : ↥(GammaH M ⊤)) :
    (iotaDeg R M ⊤ ⊤ d h ⟨jConjSL (γ : SL(2, ℤ)), jConjSL_mem_GammaH_top γ⟩ : SL(2, ℤ)) =
      jConjSL (iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)) := by
  have hdvd : (d : ℤ) ∣ ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := h.dvd_entry γ
  set γ'' : ↥(GammaH M ⊤) := ⟨jConjSL (γ : SL(2, ℤ)), jConjSL_mem_GammaH_top γ⟩ with hγ''
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have eL : ((iotaDeg R M ⊤ ⊤ d h γ'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![((γ'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0, ((γ'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * d;
         ((γ'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / d, ((γ'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1] := rfl
  have eR : ((iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * d;
         ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / d, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1] := rfl
  have eγ : ((γ'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
  rw [eL, eγ]
  simp only [jConjSL_coe]
  rw [eR]
  fin_cases i <;> fin_cases j <;> simp [jConjMat, Int.neg_ediv_of_dvd hdvd, neg_mul]

theorem periodHomPair_apply_eq (N : ℕ) [NeZero N] (f g : CuspForm (Gamma0 N) 2) (γ : Gamma0 N) :
    periodHomPair N (f, g) (Additive.ofMul γ) =
      periodMap N f (Additive.ofMul γ) + periodMap N f (Additive.ofMul (jConjGamma0 N γ)) +
      (periodMap N g (Additive.ofMul γ) - periodMap N g (Additive.ofMul (jConjGamma0 N γ))) := by
  obtain ⟨pml, hpml, hdef⟩ := periodHomPair_def N (existsPeriodMapLinear N)
  rw [hdef, LinearMap.coprod_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.id_apply, hpml, hpml]
  rfl

end OldInj

open OldInj

theorem OldInj.complex
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : LevelLE M (M * p) ⊤ ⊤ 1) (hp : LevelLE M (M * p) ⊤ ⊤ p)
    (y₁ y₂ : H1 M ⊤ ℂ)
    (hy₁ : y₁ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH M ⊤) ℂ)
    (hy₂ : y₂ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH M ⊤) ℂ)
    (h : iDegL M (M * p) ⊤ ⊤ 1 ℂ ℂ h1 y₁ + iDegL M (M * p) ⊤ ⊤ p ℂ ℂ hp y₂ = 0) :
    y₁ = 0 ∧ y₂ = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ES, hESap, hESinj, hESrange, -, -⟩ := exists_eichlerShimura_H1_top M
  obtain ⟨ES', hES'ap, hES'inj, -, -, -⟩ := exists_eichlerShimura_H1_top (M * p)

  have hcompat : ∀ (d : ℕ) [NeZero d] (hd : LevelLE M (M * p) ⊤ ⊤ d) (hdR : d * M ∣ M * p)
      (f g : CuspForm (Gamma0 M) 2),
      iDegL M (M * p) ⊤ ⊤ d ℂ ℂ hd (ES (f, g)) =
        ES' (FreyPackage.ModMCarrier.rescaleLin hdR 2 f, FreyPackage.ModMCarrier.rescaleLin hdR 2 g) := by
    intro d _ hd hdR f g
    refine AddMonoidHom.ext fun x => ?_
    induction x using Additive.rec with
    | ofMul γ' =>
    show ES (f, g) (Additive.ofMul (iotaDeg M (M * p) ⊤ ⊤ d hd γ')) = _
    rw [hESap, hES'ap, periodHomPair_apply_eq, periodHomPair_apply_eq,
      periodMap_rescaleLin_apply hdR hd f γ', periodMap_rescaleLin_apply hdR hd g γ']

    have hJ : ∀ (F : CuspForm (Gamma0 M) 2),
        periodMap (M * p) (FreyPackage.ModMCarrier.rescaleLin hdR 2 F)
          (Additive.ofMul (jConjGamma0 (M * p) ⟨(γ' : SL(2, ℤ)), GammaH_le_Gamma0 ⊤ γ'.2⟩)) =
        periodMap M F (Additive.ofMul (jConjGamma0 M ⟨(iotaDeg M (M * p) ⊤ ⊤ d hd γ' : SL(2, ℤ)),
          GammaH_le_Gamma0 ⊤ (iotaDeg M (M * p) ⊤ ⊤ d hd γ').2⟩)) := by
      intro F
      have e1 : jConjGamma0 (M * p) ⟨(γ' : SL(2, ℤ)), GammaH_le_Gamma0 ⊤ γ'.2⟩ =
          ⟨((⟨jConjSL (γ' : SL(2, ℤ)), jConjSL_mem_GammaH_top γ'⟩ : ↥(GammaH (M * p) ⊤)) : SL(2, ℤ)),
            GammaH_le_Gamma0 ⊤ (jConjSL_mem_GammaH_top γ')⟩ := Subtype.ext rfl
      have e2 : jConjGamma0 M ⟨(iotaDeg M (M * p) ⊤ ⊤ d hd γ' : SL(2, ℤ)),
          GammaH_le_Gamma0 ⊤ (iotaDeg M (M * p) ⊤ ⊤ d hd γ').2⟩ =
          ⟨(iotaDeg M (M * p) ⊤ ⊤ d hd ⟨jConjSL (γ' : SL(2, ℤ)), jConjSL_mem_GammaH_top γ'⟩ : SL(2, ℤ)),
            GammaH_le_Gamma0 ⊤ (iotaDeg M (M * p) ⊤ ⊤ d hd _).2⟩ := by
        apply Subtype.ext
        show jConjSL _ = _
        rw [iotaDeg_jConj]
      rw [e1, e2, periodMap_rescaleLin_apply hdR hd F]
    rw [hJ f, hJ g]

  have hy₁' : y₁ ∈ LinearMap.range ES := by rw [hESrange]; exact hy₁
  have hy₂' : y₂ ∈ LinearMap.range ES := by rw [hESrange]; exact hy₂
  obtain ⟨⟨f₁, g₁⟩, rfl⟩ := hy₁'
  obtain ⟨⟨f₂, g₂⟩, rfl⟩ := hy₂'
  have h1R : 1 * M ∣ M * p := ⟨p, by ring⟩
  have hpR : p * M ∣ M * p := ⟨1, by ring⟩
  rw [hcompat 1 h1 h1R, hcompat p hp hpR, ← map_add, Prod.mk_add_mk] at h
  have h0 := hES'inj (h.trans (map_zero ES').symm)
  rw [Prod.mk_eq_zero] at h0
  obtain ⟨hf, hg⟩ := h0
  rw [FreyPackage.ModMCarrier.rescaleLin_eq_levelInclusionLin h1R (dvd_mul_right M p)] at hf hg
  obtain ⟨hf₁, hf₂⟩ := FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero
    (Fact.out : p.Prime) hpM (dvd_mul_right M p) hpR f₁ f₂ hf
  obtain ⟨hg₁, hg₂⟩ := FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero
    (Fact.out : p.Prime) hpM (dvd_mul_right M p) hpR g₁ g₂ hg
  subst hf₁ hf₂ hg₁ hg₂
  exact ⟨by rw [Prod.mk_zero_zero, map_zero], by rw [Prod.mk_zero_zero, map_zero]⟩

theorem solution
    {F : Type} [Field F] [CharZero F]
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : LevelLE M (M * p) ⊤ ⊤ 1) (hp : LevelLE M (M * p) ⊤ ⊤ p)
    (y₁ y₂ : H1 M ⊤ F)
    (hy₁ : y₁ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F)
    (hy₂ : y₂ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F)
    (h : iDegL M (M * p) ⊤ ⊤ 1 F F h1 y₁ + iDegL M (M * p) ⊤ ⊤ p F F hp y₂ = 0) :
    y₁ = 0 ∧ y₂ = 0 := by

  have key : ∀ lam : Module.Dual ℚ F,
      (((algebraMap ℚ ℂ).toAddMonoidHom.comp lam.toAddMonoidHom).comp y₁ = 0) ∧
      (((algebraMap ℚ ℂ).toAddMonoidHom.comp lam.toAddMonoidHom).comp y₂ = 0) := by
    intro lam
    set Λ : F →+ ℂ := (algebraMap ℚ ℂ).toAddMonoidHom.comp lam.toAddMonoidHom with hΛ
    have hpar : ∀ y : H1 M ⊤ F, y ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F →
        Λ.comp y ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH M ⊤) ℂ := by
      intro y hy
      rw [mem_parabolicHoms_iff] at hy ⊢
      intro γ hγ
      simp [hy γ hγ]
    refine OldInj.complex M p hpM h1 hp (Λ.comp y₁) (Λ.comp y₂) (hpar y₁ hy₁) (hpar y₂ hy₂) ?_
    rw [show iDegL M (M * p) ⊤ ⊤ 1 ℂ ℂ h1 (Λ.comp y₁) = Λ.comp (iDegL M (M * p) ⊤ ⊤ 1 F F h1 y₁) from rfl,
      show iDegL M (M * p) ⊤ ⊤ p ℂ ℂ hp (Λ.comp y₂) = Λ.comp (iDegL M (M * p) ⊤ ⊤ p F F hp y₂) from rfl,
      ← AddMonoidHom.comp_add, h, AddMonoidHom.comp_zero]
  constructor
  · refine AddMonoidHom.ext fun x => ?_
    rw [AddMonoidHom.zero_apply, ← Module.forall_dual_apply_eq_zero_iff ℚ]
    intro lam
    have := DFunLike.congr_fun (key lam).1 x
    exact (algebraMap ℚ ℂ).injective (by simpa using this)
  · refine AddMonoidHom.ext fun x => ?_
    rw [AddMonoidHom.zero_apply, ← Module.forall_dual_apply_eq_zero_iff ℚ]
    intro lam
    have := DFunLike.congr_fun (key lam).2 x
    exact (algebraMap ℚ ℂ).injective (by simpa using this)

end S_CohCarrier_eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms
end P2MW
export P2MW.S_CohCarrier_eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms (solution)

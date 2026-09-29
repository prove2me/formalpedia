-- Prove2me | solution 1 for CohCarrier.exists_algHom_cornerRing_of_ringHom_heckeAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/63882b8c-c576-5702-8a0b-46419b6d7bdb

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms
import Theorems.Thm_CohCarrier_exists_basis_parabolicHoms_top_two_mul_finrank
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_algHom_cornerRing_of_ringHom_heckeAlgebra
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe"
p2m_attr_erase "simp" "ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

namespace EscompC5

open IharaLemma

section Abstract

variable {𝒪 : Type} [CommRing 𝒪]

theorem exists_corner_point {R : Type} [CommRing R] [Algebra 𝒪 R]
    {K : Type} [Field K] [Algebra 𝒪 K] (hk : Function.Surjective (algebraMap 𝒪 K))
    (χ : R →ₐ[𝒪] K) (Sp : IdempotentSplitting R) :
    ∃ (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] K),
      ∀ r : R, πk (Sp.toCornerRing i₀ r) = χ r := by
  have hχsurj : Function.Surjective χ := fun y => by
    obtain ⟨a, rfl⟩ := hk y
    exact ⟨algebraMap 𝒪 R a, χ.commutes a⟩
  have hmax : (RingHom.ker χ.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective χ.toRingHom hχsurj
  obtain ⟨i₀, hi₀⟩ := Sp.exists_eq _ hmax
  have hker : ∀ r : R, r ∈ Sp.𝔪 i₀ ↔ χ r = 0 := fun r => by
    rw [hi₀, RingHom.mem_ker]
    rfl

  have hunit : ∀ s : (Sp.𝔪 i₀).primeCompl, IsUnit (χ.toRingHom s) := by
    intro s
    have hs : (s : R) ∉ Sp.𝔪 i₀ := Ideal.mem_primeCompl_iff.mp s.2
    exact isUnit_iff_ne_zero.mpr fun h0 => hs ((hker _).mpr h0)

  let π₀ : Sp.CornerRing i₀ →+* K := IsLocalization.lift (M := (Sp.𝔪 i₀).primeCompl) hunit
  have hπ₀ : ∀ r : R, π₀ (algebraMap R (Sp.CornerRing i₀) r) = χ r := fun r =>
    IsLocalization.lift_eq hunit r
  have halg : ∀ r : R, algebraMap R (Sp.CornerRing i₀) r = Sp.toCornerRing i₀ r := fun _ => rfl
  refine ⟨i₀, { π₀ with commutes' := fun a => ?_ }, fun r => ?_⟩
  · show π₀ (Sp.toCornerRing i₀ (algebraMap 𝒪 R a)) = algebraMap 𝒪 K a
    rw [← halg, hπ₀, AlgHom.commutes]
  · show π₀ (Sp.toCornerRing i₀ r) = χ r
    rw [← halg, hπ₀]

variable {V : Type} [AddCommGroup V] [Module 𝒪 V]
variable {R : Type} [CommRing R] [Algebra 𝒪 R] (ρV : R →ₐ[𝒪] Module.End 𝒪 V)
variable (Vp : Submodule 𝒪 V) (hstab : ∀ r : R, ∀ v ∈ Vp, ρV r v ∈ Vp)

def res : R →ₐ[𝒪] Module.End 𝒪 Vp where
  toFun r := (ρV r).restrict (hstab r)
  map_one' := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    show ρV 1 v = v
    rw [map_one]; rfl
  map_mul' r s := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    show ρV (r * s) v = ρV r (ρV s v)
    rw [map_mul]; rfl
  map_zero' := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    show ρV 0 v = 0
    rw [map_zero]; rfl
  map_add' r s := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    show ρV (r + s) v = ρV r v + ρV s v
    rw [map_add]; rfl
  commutes' a := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    show ρV (algebraMap 𝒪 R a) v = ((algebraMap 𝒪 (Module.End 𝒪 Vp) a v : Vp) : V)
    rw [AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul]

@[scoped simp] theorem res_apply_coe (r : R) (v : Vp) : ((res ρV Vp hstab r v : Vp) : V) = ρV r v := rfl

theorem exists_algHom_of_generators
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Λ : B →ₐ[𝒪] Module.End 𝒪 Vp) (hΛ : Function.Injective Λ)
    {K : Type} [CommRing K] [Algebra 𝒪 K] (χB : B →ₐ[𝒪] K)
    (G : Set R) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hgen : ∀ g ∈ G, ∃ b : B, Λ b = res ρV Vp hstab g) :
    ∃ χR : R →ₐ[𝒪] K, ∀ (r : R) (b : B), Λ b = res ρV Vp hstab r → χR r = χB b := by
  classical
  set resA := res ρV Vp hstab with hresA

  have hres_mem : ∀ r : R, resA r ∈ Λ.range := by
    have hle : Algebra.adjoin 𝒪 G ≤ (Λ.range).comap resA :=
      Algebra.adjoin_le fun g hg => by
        obtain ⟨b, hb⟩ := hgen g hg
        exact ⟨b, hb⟩
    intro r
    have hr : r ∈ Algebra.adjoin 𝒪 G := hG ▸ Algebra.mem_top
    exact hle hr

  let eΛ := AlgEquiv.ofInjective Λ hΛ
  let f : R →ₐ[𝒪] B := (eΛ.symm : ↥Λ.range →ₐ[𝒪] B).comp (resA.codRestrict Λ.range hres_mem)
  have hΛf : ∀ r, Λ (f r) = resA r := by
    intro r
    show Λ (eΛ.symm ⟨resA r, hres_mem r⟩) = resA r
    have h := AlgEquiv.ofInjective_apply Λ hΛ (eΛ.symm ⟨resA r, hres_mem r⟩)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  have hf_of : ∀ b r, Λ b = resA r → f r = b := fun b r h => hΛ (by rw [hΛf, h])
  refine ⟨χB.comp f, fun r b hbr => ?_⟩
  show χB (f r) = χB b
  rw [hf_of b r hbr]

end Abstract

section Furniture

open CohCarrier
open scoped MatrixGroups

theorem heckeT_comp (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {A A' : Type} [AddCommGroup A] [AddCommGroup A'] (f : A →+ A') (φ : H1 M H A) :
    heckeT M H ℓ A' (f.comp φ) = f.comp (heckeT M H ℓ A φ) := by
  ext g
  simp only [heckeT, AddMonoidHom.coe_mk, ZeroHom.coe_mk, MonoidHom.toAdditiveLeft_apply_apply,
    AddMonoidHom.coe_comp, Function.comp_apply, MonoidHom.transfer_def _ default,
    Subgroup.leftTransversals.diff, toAdd_prod, MonoidHom.coe_comp,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, map_sum]

variable (N : ℕ)

def castPar (Rr A : Type) [Semiring Rr] [AddCommGroup A] [Module Rr A] (c : ℤ →+ A) :
    ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ) →+
      ↥(ModularCurve.Period.parabolicHoms Rr (GammaH N ⊤) A) where
  toFun φ := ⟨c.comp (φ : H1 N ⊤ ℤ), fun γ hγ => by
    show c ((φ : H1 N ⊤ ℤ) (Additive.ofMul γ)) = 0
    rw [φ.2 γ hγ, map_zero]⟩
  map_zero' := by apply Subtype.ext; ext γ; simp
  map_add' φ ψ := by apply Subtype.ext; ext γ; simp

@[scoped simp] theorem coe_castPar (Rr A : Type) [Semiring Rr] [AddCommGroup A] [Module Rr A] (c : ℤ →+ A)
    (φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) :
    ((castPar N Rr A c φ : ↥(ModularCurve.Period.parabolicHoms Rr (GammaH N ⊤) A)) : H1 N ⊤ A) =
      c.comp (φ : H1 N ⊤ ℤ) := rfl

theorem diamondL_top_apply [NeZero N] (𝒪 : Type) [CommRing 𝒪] (d : (ZMod N)ˣ) (φ : H1 N ⊤ 𝒪) :
    diamondL N ⊤ 𝒪 d φ = φ := by
  show diamondRaw N ⊤ 𝒪 (Classical.choose (gamma0Units_surjective N d)) φ = φ
  set σ := Classical.choose (gamma0Units_surjective N d)
  have hσ : (σ : SL(2, ℤ)) ∈ GammaH N ⊤ := by rw [GammaH_top]; exact σ.2
  ext γ
  show φ (Additive.ofMul (conjHom N ⊤ σ (Additive.toMul γ))) = φ γ
  have hconj : conjHom N ⊤ σ (Additive.toMul γ) =
      ⟨σ, hσ⟩ * Additive.toMul γ * ⟨σ, hσ⟩⁻¹ := Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  simp

end Furniture

section BaseChange

open CohCarrier
open scoped TensorProduct

variable (N : ℕ) (𝒪 : Type) [CommRing 𝒪]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (bZ : Module.Basis I ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
variable (bO : Module.Basis I 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪))
variable (hb : ∀ i, (bO i : H1 N ⊤ 𝒪) = (Int.castAddHom 𝒪).comp (bZ i : H1 N ⊤ ℤ))

noncomputable def ιO : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ) →+*
    Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :=
  (Matrix.toLinAlgEquiv bO).toRingEquiv.toRingHom.comp
    ((Int.castRingHom 𝒪).mapMatrix.comp (LinearMap.toMatrixAlgEquiv bZ).toRingEquiv.toRingHom)

theorem ιO_apply (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) :
    ιO N 𝒪 bZ bO f =
      Matrix.toLinAlgEquiv bO ((LinearMap.toMatrixAlgEquiv bZ f).map (Int.castRingHom 𝒪)) := rfl

theorem ιO_apply_basis (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
    (j : I) :
    ιO N 𝒪 bZ bO f (bO j) = ∑ i, ((LinearMap.toMatrixAlgEquiv bZ f i j : ℤ) : 𝒪) • bO i := by
  rw [ιO_apply, Matrix.toLinAlgEquiv_self]
  rfl

include hb in
omit [Fintype I] [DecidableEq I] in
theorem castPar_basis (i : I) : castPar N 𝒪 𝒪 (Int.castAddHom 𝒪) (bZ i) = bO i :=
  Subtype.ext (hb i).symm

include hb in

theorem ιO_castPar (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
    (x : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) :
    ιO N 𝒪 bZ bO f (castPar N 𝒪 𝒪 (Int.castAddHom 𝒪) x) =
      castPar N 𝒪 𝒪 (Int.castAddHom 𝒪) (f x) := by

  set c := castPar N 𝒪 𝒪 (Int.castAddHom 𝒪) with hc
  let G₁ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ) →ₗ[ℤ]
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :=
    ((ιO N 𝒪 bZ bO f).toAddMonoidHom.comp c).toIntLinearMap
  let G₂ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ) →ₗ[ℤ]
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :=
    (c.comp f.toAddMonoidHom).toIntLinearMap
  suffices h : G₁ = G₂ from LinearMap.congr_fun h x
  apply bZ.ext
  intro j
  show ιO N 𝒪 bZ bO f (c (bZ j)) = c (f (bZ j))
  rw [hc, castPar_basis N 𝒪 bZ bO hb, ιO_apply_basis]
  conv_rhs => rw [← bZ.sum_repr (f (bZ j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, castPar_basis N 𝒪 bZ bO hb, LinearMap.toMatrixAlgEquiv_apply]
  exact Int.cast_smul_eq_zsmul 𝒪 (M := ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) _ _

include hb in

theorem coe_ιO_apply_of_heckeT (n : ℕ) [NeZero n]
    (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
    (hf : ∀ φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ),
      ((f φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) : H1 N ⊤ ℤ) =
        heckeT N ⊤ n ℤ (φ : H1 N ⊤ ℤ))
    (φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) :
    ((ιO N 𝒪 bZ bO f φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) : H1 N ⊤ 𝒪) =
      heckeT N ⊤ n 𝒪 (φ : H1 N ⊤ 𝒪) := by
  let F₁ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) →ₗ[𝒪] H1 N ⊤ 𝒪 :=
    (Submodule.subtype _) ∘ₗ (ιO N 𝒪 bZ bO f)
  let F₂ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) →ₗ[𝒪] H1 N ⊤ 𝒪 :=
    (heckeTL N ⊤ 𝒪 n) ∘ₗ (Submodule.subtype _)
  suffices h : F₁ = F₂ from LinearMap.congr_fun h φ
  apply bO.ext
  intro i
  show ((ιO N 𝒪 bZ bO f (bO i) : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) :
      H1 N ⊤ 𝒪) = heckeT N ⊤ n 𝒪 (bO i : H1 N ⊤ 𝒪)
  rw [← castPar_basis N 𝒪 bZ bO hb i, ιO_castPar N 𝒪 bZ bO hb, coe_castPar, hf, coe_castPar,
    heckeT_comp]

end BaseChange

section Lambda

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open CohCarrier CuspForm
open scoped TensorProduct

variable (N : ℕ) [NeZero N] (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (bZ : Module.Basis I ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
variable (bO : Module.Basis I 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪))
variable (ρ : ↥(heckeAlgebra N 2 S) →+*
  Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))

def intAlgHom {A₁ A₂ : Type} [Semiring A₁] [Semiring A₂] [Algebra ℤ A₁] [Algebra ℤ A₂]
    (g : A₁ →+* A₂) : A₁ →ₐ[ℤ] A₂ :=
  { g with commutes' := fun n =>
      RingHom.congr_fun (RingHom.ext_int (g.comp (algebraMap ℤ A₁)) (algebraMap ℤ A₂)) n }

@[scoped simp] theorem intAlgHom_apply {A₁ A₂ : Type} [Semiring A₁] [Semiring A₂] [Algebra ℤ A₁]
    [Algebra ℤ A₂] (g : A₁ →+* A₂) (x : A₁) : intAlgHom g x = g x := rfl

noncomputable def κ : 𝒪 ⊗[ℤ] Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ) →ₐ[𝒪]
    Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :=
  Algebra.TensorProduct.lift (Algebra.ofId 𝒪 _) (intAlgHom (ιO N 𝒪 bZ bO))
    fun a _ => Algebra.commute_algebraMap_left a _

omit [NeZero N] in
theorem κ_tmul (a : 𝒪) (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) :
    κ N 𝒪 bZ bO (a ⊗ₜ f) = a • ιO N 𝒪 bZ bO f := by
  rw [κ, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

omit [NeZero N] in
theorem κ_tmul_eq [IsDomain 𝒪] [CharZero 𝒪] (a : 𝒪)
    (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) :
    κ N 𝒪 bZ bO (a ⊗ₜ f) = Matrix.toLinAlgEquiv bO ((matrixEquivTensor I ℤ 𝒪).symm
      (LinearMap.lTensor 𝒪 (LinearMap.toMatrixAlgEquiv bZ).toLinearEquiv.toLinearMap (a ⊗ₜ f))) := by
  have h2 : (LinearMap.lTensor 𝒪 (LinearMap.toMatrixAlgEquiv bZ).toLinearEquiv.toLinearMap (a ⊗ₜ f))
      = a ⊗ₜ (LinearMap.toMatrixAlgEquiv bZ f) := by
    rw [LinearMap.lTensor_tmul]; rfl
  have h3 : (matrixEquivTensor I ℤ 𝒪).symm (a ⊗ₜ (LinearMap.toMatrixAlgEquiv bZ f))
      = a • (LinearMap.toMatrixAlgEquiv bZ f).map (algebraMap ℤ 𝒪) :=
    matrixEquivTensor_apply_symm I ℤ 𝒪 a _
  have h4 : Matrix.toLinAlgEquiv bO (a • (LinearMap.toMatrixAlgEquiv bZ f).map (algebraMap ℤ 𝒪))
      = a • Matrix.toLinAlgEquiv bO ((LinearMap.toMatrixAlgEquiv bZ f).map (algebraMap ℤ 𝒪)) :=
    map_smul _ _ _
  rw [h2, h3, h4, κ_tmul, ιO_apply, algebraMap_int_eq]

omit [NeZero N] in
theorem κ_apply_eq [IsDomain 𝒪] [CharZero 𝒪]
    (x : 𝒪 ⊗[ℤ] Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) :
    κ N 𝒪 bZ bO x = Matrix.toLinAlgEquiv bO ((matrixEquivTensor I ℤ 𝒪).symm
      (LinearMap.lTensor 𝒪 (LinearMap.toMatrixAlgEquiv bZ).toLinearEquiv.toLinearMap x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a f => exact κ_tmul_eq N 𝒪 bZ bO a f
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NeZero N] in

theorem κ_injective [IsDomain 𝒪] [CharZero 𝒪] : Function.Injective (κ N 𝒪 bZ bO) := by
  intro x y hxy
  rw [κ_apply_eq, κ_apply_eq] at hxy
  have h1 := (matrixEquivTensor I ℤ 𝒪).symm.injective ((Matrix.toLinAlgEquiv bO).injective hxy)
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (LinearMap.toMatrixAlgEquiv bZ).toLinearEquiv.injective h1

noncomputable def Λ₀ : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S) →ₐ[𝒪]
    Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :=
  Algebra.TensorProduct.lift (Algebra.ofId 𝒪 _) (intAlgHom ((ιO N 𝒪 bZ bO).comp ρ))
    fun a _ => Algebra.commute_algebraMap_left a _

theorem Λ₀_tmul (a : 𝒪) (t : ↥(heckeAlgebra N 2 S)) :
    Λ₀ N S 𝒪 bZ bO ρ (a ⊗ₜ t) = a • ιO N 𝒪 bZ bO (ρ t) := by
  rw [Λ₀, Algebra.TensorProduct.lift_tmul, Algebra.smul_def]
  rfl

theorem Λ₀_apply_eq (x : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) :
    Λ₀ N S 𝒪 bZ bO ρ x = κ N 𝒪 bZ bO (LinearMap.lTensor 𝒪 (intAlgHom ρ).toLinearMap x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a y => rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, intAlgHom_apply, κ_tmul, Λ₀_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Λ₀_injective [IsDomain 𝒪] [CharZero 𝒪] (hρ : Function.Injective ρ) :
    Function.Injective (Λ₀ N S 𝒪 bZ bO ρ) := by
  have hm : Function.Injective (LinearMap.lTensor 𝒪 (intAlgHom ρ).toLinearMap) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hρ
  intro x y hxy
  rw [Λ₀_apply_eq, Λ₀_apply_eq] at hxy
  exact hm (κ_injective N 𝒪 bZ bO hxy)

end Lambda

section Concrete

open CohCarrier CuspForm IharaLemma
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable (N : ℕ) [NeZero N] (S : Set ℕ) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
variable (hcomm : ∀ g h : Gen N S,
  opFamily N ⊤ S 𝒪 g * opFamily N ⊤ S 𝒪 h = opFamily N ⊤ S 𝒪 h * opFamily N ⊤ S 𝒪 g)
variable (θbar : Gen N S → k)
variable {I : Type} [Fintype I] [DecidableEq I]
variable (bZ : Module.Basis I ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
variable (bO : Module.Basis I 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪))
variable (hb : ∀ i, (bO i : H1 N ⊤ 𝒪) = (Int.castAddHom 𝒪).comp (bZ i : H1 N ⊤ ℤ))
variable (ρ : ↥(heckeAlgebra N 2 S) →+*
  Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
variable (hρT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S)
    (φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)),
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((ρ (heckeAlgebra.T hℓ hℓN hℓS) φ :
      ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) : H1 N ⊤ ℤ) = heckeT N ⊤ ℓ ℤ φ)
variable (hρU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S)
    (φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)),
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ((ρ (heckeAlgebra.U hq hqN hqS) φ :
      ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) : H1 N ⊤ ℤ) = heckeT N ⊤ q ℤ φ)

include hb hρT in
theorem coe_ιO_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S)
    (φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((ιO N 𝒪 bZ bO (ρ (heckeAlgebra.T hℓ hℓN hℓS)) φ :
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) : H1 N ⊤ 𝒪) = heckeT N ⊤ ℓ 𝒪 φ :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  coe_ιO_apply_of_heckeT N 𝒪 bZ bO hb ℓ _ (hρT ℓ hℓ hℓN hℓS) φ

include hb hρU in
theorem coe_ιO_U (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S)
    (φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ((ιO N 𝒪 bZ bO (ρ (heckeAlgebra.U hq hqN hqS)) φ :
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) : H1 N ⊤ 𝒪) = heckeT N ⊤ q 𝒪 φ :=
  haveI : NeZero q := ⟨hq.ne_zero⟩
  coe_ιO_apply_of_heckeT N 𝒪 bZ bO hb q _ (hρU q hq hqN hqS) φ

include hS hb hρT hρU in
open scoped IsMulCommutative in

theorem stab (r : ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
    (v : H1 N ⊤ 𝒪) (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :
    (r : Module.End 𝒪 (H1 N ⊤ 𝒪)) v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪 := by
  obtain ⟨x, hx⟩ := r
  revert v
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    cases g with
    | T ℓ hℓ hℓS hℓN =>
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      show heckeT N ⊤ ℓ 𝒪 v ∈ _
      rw [← coe_ιO_T N S 𝒪 bZ bO hb ρ hρT ℓ hℓ hℓN hℓS ⟨v, hv⟩]
      exact SetLike.coe_mem _
    | U q hq hqN =>
      haveI : NeZero q := ⟨hq.ne_zero⟩
      show heckeT N ⊤ q 𝒪 v ∈ _
      rw [← coe_ιO_U N S 𝒪 bZ bO hb ρ hρU q hq hqN (hS q hq hqN) ⟨v, hv⟩]
      exact SetLike.coe_mem _
    | dia d =>
      show diamondL N ⊤ 𝒪 d v ∈ _
      rw [diamondL_top_apply]
      exact hv
  | algebraMap a =>
    intro v hv
    show (algebraMap 𝒪 (Module.End 𝒪 (H1 N ⊤ 𝒪)) a) v ∈ _
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ a hv
  | add x y hx hy ihx ihy =>
    intro v hv
    exact Submodule.add_mem _ (ihx v hv) (ihy v hv)
  | mul x y hx hy ihx ihy =>
    intro v hv
    exact ihx _ (ihy v hv)

open scoped IsMulCommutative in

noncomputable def valC :
    @AlgHom 𝒪 ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra (Module.End 𝒪 (H1 N ⊤ 𝒪)) _
      CommSemiring.toSemiring _ inferInstance _ :=
  (hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra.val

open scoped IsMulCommutative in
theorem valC_apply (r : ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra) (v : H1 N ⊤ 𝒪) :
    valC N S 𝒪 k hcomm θbar r v = (r : Module.End 𝒪 (H1 N ⊤ 𝒪)) v := rfl

include hS hb hρT hρU in
open scoped IsMulCommutative in

theorem hstab :
    ∀ r : ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra,
      ∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪,
        valC N S 𝒪 k hcomm θbar r v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪 :=
  fun r v hv => stab N S hS 𝒪 k hcomm θbar bZ bO hb ρ hρT hρU r v hv

include hb hρT in
open scoped IsMulCommutative in

theorem Λ₀_T
    (hst : ∀ r : ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra,
      ∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪,
        valC N S 𝒪 k hcomm θbar r v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S) :
    Λ₀ N S 𝒪 bZ bO ρ (1 ⊗ₜ heckeAlgebra.T hℓ hℓN hℓS) =
      res (valC N S 𝒪 k hcomm θbar) (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst
        ⟨(hdata N ⊤ S 𝒪 k hcomm θbar).op (Gen.T ℓ hℓ hℓS hℓN),
          Algebra.subset_adjoin (Set.mem_range_self _)⟩ := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rw [Λ₀_tmul, one_smul, res_apply_coe]
  exact coe_ιO_T N S 𝒪 bZ bO hb ρ hρT ℓ hℓ hℓN hℓS φ

include hb hρU in
open scoped IsMulCommutative in

theorem Λ₀_U
    (hst : ∀ r : ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra,
      ∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪,
        valC N S 𝒪 k hcomm θbar r v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S) :
    Λ₀ N S 𝒪 bZ bO ρ (1 ⊗ₜ heckeAlgebra.U hq hqN hqS) =
      res (valC N S 𝒪 k hcomm θbar) (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst
        ⟨(hdata N ⊤ S 𝒪 k hcomm θbar).op (Gen.U q hq hqN),
          Algebra.subset_adjoin (Set.mem_range_self _)⟩ := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rw [Λ₀_tmul, one_smul, res_apply_coe]
  exact coe_ιO_U N S 𝒪 bZ bO hb ρ hρU q hq hqN hqS φ

open scoped IsMulCommutative in

theorem gen_dia_eq_one (d : (ZMod N)ˣ) :
    (⟨(hdata N ⊤ S 𝒪 k hcomm θbar).op (Gen.dia d), Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
      ↥(hdata N ⊤ S 𝒪 k hcomm θbar).opSubalgebra) = 1 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro φ
  exact diamondL_top_apply N 𝒪 d φ

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
variable (θ : ↥(heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)

noncomputable def χ₀ : (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) →ₐ[𝒪] IsLocalRing.ResidueField 𝒪 :=
  { (residualCharacter N S 𝒪 θ).toRingHom with
    commutes' := fun a => by
      show residualCharacter N S 𝒪 θ (algebraMap 𝒪 _ a) = _
      rw [residualCharacter_algebraMap]
      rfl }

theorem χ₀_tmul (a : 𝒪) (t : ↥(heckeAlgebra N 2 S)) :
    χ₀ N S 𝒪 θ (a ⊗ₜ t) = IsLocalRing.residue 𝒪 a * θ t :=
  residualCharacter_tmul N S 𝒪 θ a t

end Concrete

section Final

open CohCarrier CuspForm IharaLemma
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open scoped IsMulCommutative in
theorem main
    (N : ℕ) [NeZero N] (S : Set ℕ) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 h =
        CohCarrier.opFamily N ⊤ S 𝒪 h * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N),
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    (hθU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
      θbar (CohCarrier.Gen.U q hq hqN) = θ (CuspForm.heckeAlgebra.U hq hqN (hS q hq hqN)))
    (hθdia : ∀ d : (ZMod N)ˣ, θbar (CohCarrier.Gen.dia d) = 1)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra) :
    ∃ (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪),
      ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
        ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
          Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g := by
  classical

  obtain ⟨bZ, hbZ⟩ := CohCarrier.exists_basis_parabolicHoms_top_two_mul_finrank N
  obtain ⟨bO, hbO⟩ := hbZ 𝒪
  obtain ⟨-, ρ, hρinj, hρT, hρU⟩ :=
    CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms N S
  have hk : Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField 𝒪)) :=
    Ideal.Quotient.mk_surjective

  have hst := hstab N S hS 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar bZ bO hbO ρ hρT hρU
  have hΛ := Λ₀_injective N S 𝒪 bZ bO ρ hρinj
  have hΛT := Λ₀_T N S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar bZ bO hbO ρ hρT hst
  have hΛU := Λ₀_U N S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar bZ bO hbO ρ hρU hst

  have hG : Algebra.adjoin 𝒪 (Subtype.val ⁻¹'
      Set.range (CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op :
      Set ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  have hgen : ∀ g ∈ (Subtype.val ⁻¹'
      Set.range (CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op :
      Set ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra),
      ∃ bb : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S), Λ₀ N S 𝒪 bZ bO ρ bb =
        res (valC N S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar)
          (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst g := by
    rintro ⟨x, hxmem⟩ ⟨g, hg⟩
    dsimp only at hg
    subst hg
    cases g with
    | T ℓ hℓ hℓS hℓN => exact ⟨1 ⊗ₜ heckeAlgebra.T hℓ hℓN hℓS, hΛT ℓ hℓ hℓN hℓS⟩
    | U q hq hqN => exact ⟨1 ⊗ₜ heckeAlgebra.U hq hqN (hS q hq hqN), hΛU q hq hqN (hS q hq hqN)⟩
    | dia d =>
      have h1 : (⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op
          (Gen.dia d), hxmem⟩ :
          ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra) = 1 :=
        gen_dia_eq_one N S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar d
      refine ⟨1, ?_⟩
      rw [h1, map_one, map_one]

  obtain ⟨χR, hχR⟩ := exists_algHom_of_generators
    (valC N S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar)
    (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst
    (Λ₀ N S 𝒪 bZ bO ρ) hΛ (χ₀ N S 𝒪 θ) _ hG hgen

  obtain ⟨i₀, πk, hπk⟩ := exists_corner_point hk χR Sp
  refine ⟨i₀, πk, fun g => ?_⟩
  rw [hπk]
  cases g with
  | T ℓ hℓ hℓS hℓN =>
    rw [hχR _ _ (hΛT ℓ hℓ hℓN hℓS), χ₀_tmul, map_one, one_mul, hθT]
  | U q hq hqN =>
    rw [hχR _ _ (hΛU q hq hqN (hS q hq hqN)), χ₀_tmul, map_one, one_mul, hθU]
  | dia d =>
    rw [gen_dia_eq_one N S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar d, map_one, hθdia]

end Final

end EscompC5
p2m_reactivate "P2MW.S_CohCarrier_exists_algHom_cornerRing_of_ringHom_heckeAlgebra.EscompC5"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
open scoped IsMulCommutative in
theorem solution
    (N : ℕ) [NeZero N] (S : Set ℕ) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 h =
        CohCarrier.opFamily N ⊤ S 𝒪 h * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N),
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    (hθU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
      θbar (CohCarrier.Gen.U q hq hqN) = θ (CuspForm.heckeAlgebra.U hq hqN (hS q hq hqN)))
    (hθdia : ∀ d : (ZMod N)ˣ, θbar (CohCarrier.Gen.dia d) = 1)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra) :
    ∃ (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪),
      ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
        ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
          Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g :=
  EscompC5.main N S hS 𝒪 θ hcomm θbar hθT hθU hθdia Sp

end S_CohCarrier_exists_algHom_cornerRing_of_ringHom_heckeAlgebra
end P2MW
export P2MW.S_CohCarrier_exists_algHom_cornerRing_of_ringHom_heckeAlgebra (solution)

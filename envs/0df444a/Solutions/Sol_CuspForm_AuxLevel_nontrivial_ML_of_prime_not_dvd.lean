-- Prove2me | solution 1 for CuspForm.AuxLevel.nontrivial_ML_of_prime_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/10cdefa0-f3ec-5b52-88c2-c32b122bf80a

import Definitions.Def_CuspForm_AuxLevelHeckeModule
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms
import Theorems.Thm_CohCarrier_exists_basis_parabolicHoms_top_two_mul_finrank
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Support
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_AuxLevel_nontrivial_ML_of_prime_not_dvd
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe"
p2m_attr_erase "simp" "ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

namespace AuxLevelOccupancy

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

variable (hb : ∀ i, (bO i : H1 N ⊤ 𝒪) = (Int.castAddHom 𝒪).comp (bZ i : H1 N ⊤ ℤ))
variable (hρT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S)
    (φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)),
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((ρ (heckeAlgebra.T hℓ hℓN hℓS) φ :
      ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) : H1 N ⊤ ℤ) = heckeT N ⊤ ℓ ℤ φ)

include hb hρT in

theorem coe_Λ₀_one_tmul_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S)
    (φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((Λ₀ N S 𝒪 bZ bO ρ (1 ⊗ₜ heckeAlgebra.T hℓ hℓN hℓS) φ :
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) : H1 N ⊤ 𝒪) = heckeT N ⊤ ℓ 𝒪 φ := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [Λ₀_tmul, one_smul]
  exact coe_ιO_apply_of_heckeT N 𝒪 bZ bO hb ℓ _ (hρT ℓ hℓ hℓN hℓS) φ

variable (k : Type) [Field k] [Algebra 𝒪 k]
variable (θ : ↥(heckeAlgebra N 2 S) →+* k)

noncomputable def χ₀ : (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) →ₐ[𝒪] k :=
  Algebra.TensorProduct.lift (Algebra.ofId 𝒪 k) (intAlgHom θ) fun _ _ => Commute.all _ _

theorem χ₀_tmul (a : 𝒪) (t : ↥(heckeAlgebra N 2 S)) :
    χ₀ N S 𝒪 k θ (a ⊗ₜ t) = algebraMap 𝒪 k a * θ t := by
  rw [χ₀, Algebra.TensorProduct.lift_tmul]
  rfl

end Lambda

section Restriction

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable (N r : ℕ)

theorem levelLE_aux : LevelLE N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1 :=
  ⟨dvd_mul_right N r, one_dvd _, fun _ _ => Subgroup.mem_top _⟩

variable (𝒪 : Type) [CommRing 𝒪]

noncomputable def resO : H1 N ⊤ 𝒪 →ₗ[𝒪] CuspForm.AuxLevel.Carrier N r 𝒪 :=
  iDegL N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1 𝒪 𝒪 (levelLE_aux N r)

theorem resO_apply (φ : H1 N ⊤ 𝒪) :
    resO N r 𝒪 φ = iDeg' N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1 𝒪 (levelLE_aux N r) φ := rfl

theorem resO_apply_ofMul (φ : H1 N ⊤ 𝒪) (δ : ↥(GammaH (N * r) (CuspForm.AuxLevel.subgroup N r))) :
    resO N r 𝒪 φ (Additive.ofMul δ) =
      φ (Additive.ofMul (iotaDeg N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1 (levelLE_aux N r) δ)) :=
  rfl

theorem resO_injective [NeZero N] (hr0 : r ≠ 0) [IsDomain 𝒪] [CharZero 𝒪] :
    Function.Injective (resO N r 𝒪) := by
  haveI hNr : NeZero (N * r) := ⟨mul_ne_zero (NeZero.ne N) hr0⟩
  haveI : NeZero (N * r * 1) := ⟨by rw [mul_one]; exact NeZero.ne (N * r)⟩
  refine (injective_iff_map_eq_zero (resO N r 𝒪)).mpr fun φ hφ => ?_
  apply AddMonoidHom.ext
  intro γ
  set K : Subgroup ↥(GammaH N ⊤) := (Gamma (N * r * 1)).subgroupOf (GammaH N ⊤) with hK
  haveI hKfi : K.FiniteIndex := inferInstance
  obtain ⟨n, hn, -, hmem⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero hKfi.index_ne_zero (Additive.toMul γ)
  obtain ⟨δ, hδ⟩ :=
    Gamma_subgroupOf_le_range_iotaDeg N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1
      (levelLE_aux N r) hmem
  have h1 : φ (Additive.ofMul ((Additive.toMul γ) ^ n)) = 0 := by
    rw [← hδ, ← resO_apply_ofMul, hφ, AddMonoidHom.zero_apply]
  rw [ofMul_pow, map_nsmul, ofMul_toMul, nsmul_eq_mul] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd (Nat.cast_eq_zero.mp h) hn.ne'
  · rw [h, AddMonoidHom.zero_apply]

theorem resO_heckeT (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓNr : ¬ ℓ ∣ N * r) (φ : H1 N ⊤ 𝒪) :
    resO N r 𝒪 (heckeT N ⊤ ℓ 𝒪 φ) =
      heckeT (N * r) (CuspForm.AuxLevel.subgroup N r) ℓ 𝒪 (resO N r 𝒪 φ) := by
  rw [resO_apply, resO_apply]
  exact CohCarrier.iDeg_heckeT_comm_of_coprime (levelLE_aux N r) (Nat.coprime_one_right ℓ) hℓ hℓNr φ

end Restriction

section FreeAlg

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open CohCarrier CuspForm
open scoped TensorProduct

variable (N : ℕ) [NeZero N] (S : Set ℕ) (r : ℕ) (hr : r.Prime)
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
variable (θ : ↥(heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
variable (hc : AuxLevel.OpComm N r S 𝒪)

noncomputable def Φ : (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg →ₐ[𝒪] 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S) :=
  MvPolynomial.aeval fun g : AuxLevel.Gen N r S =>
    (1 : 𝒪) ⊗ₜ[ℤ] (heckeAlgebra.T g.prime g.not_dvd g.notMem : ↥(heckeAlgebra N 2 S))

omit [CharZero 𝒪] in
theorem Φ_X (g : AuxLevel.Gen N r S) :
    Φ N S r 𝒪 θ hc (MvPolynomial.X g) =
      (1 : 𝒪) ⊗ₜ[ℤ] (heckeAlgebra.T g.prime g.not_dvd g.notMem : ↥(heckeAlgebra N 2 S)) :=
  MvPolynomial.aeval_X _ g

omit [CharZero 𝒪] in

theorem χ₀_comp_Φ :
    (χ₀ N S 𝒪 (IsLocalRing.ResidueField 𝒪) θ).comp (Φ N S r 𝒪 θ hc) =
      (AuxLevel.heckeData N r S 𝒪 θ hc).thetaTilde := by
  apply MvPolynomial.algHom_ext
  intro g
  rw [AlgHom.comp_apply, Φ_X, χ₀_tmul, map_one, one_mul]
  show _ = MvPolynomial.aeval (AuxLevel.heckeData N r S 𝒪 θ hc).θbar (MvPolynomial.X g)
  rw [MvPolynomial.aeval_X]
  rfl

omit [CharZero 𝒪] in

private theorem _root_.AuxLevelOccupancy.smul_def (p : (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg) (v : AuxLevel.Carrier N r 𝒪) :
    p • v = (AuxLevel.heckeData N r S 𝒪 θ hc).opAlgHom p v := rfl

p2m_export "AuxLevelOccupancy" "smul_def"
omit [CharZero 𝒪] in

theorem X_smul (g : AuxLevel.Gen N r S) (v : AuxLevel.Carrier N r 𝒪) :
    (MvPolynomial.X g : (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg) • v =
      (haveI : NeZero g.ℓ := ⟨g.prime.ne_zero⟩
       heckeT (N * r) (AuxLevel.subgroup N r) g.ℓ 𝒪 v) := by
  rw [smul_def, HeckeData.opAlgHom_X]
  rfl

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

include hr in
omit [NeZero N] in

theorem not_dvd_mul (g : AuxLevel.Gen N r S) : ¬ g.ℓ ∣ N * r := by
  intro h
  rcases (Nat.Prime.dvd_mul g.prime).mp h with hN | hR
  · exact g.not_dvd hN
  · exact g.ne ((Nat.prime_dvd_prime_iff_eq g.prime hr).mp hR)

include hr hb hρT in
omit [CharZero 𝒪] in

theorem resO_Λ₀_Φ (p : (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg)
    (φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) :
    resO N r 𝒪 ((Λ₀ N S 𝒪 bZ bO ρ (Φ N S r 𝒪 θ hc p) φ :
        ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) : H1 N ⊤ 𝒪) =
      p • resO N r 𝒪 (φ : H1 N ⊤ 𝒪) := by
  revert φ
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro φ
    have hC : (MvPolynomial.C a : (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg) =
        algebraMap 𝒪 (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg a := rfl
    rw [hC, AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Submodule.coe_smul,
      map_smul, HeckeData.algebraMap_freeAlg_smul]
  | add p q hp hq =>
    intro φ
    rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, map_add, hp, hq, add_smul]
  | mul_X p g hp =>
    intro φ
    haveI : NeZero g.ℓ := ⟨g.prime.ne_zero⟩
    rw [map_mul, map_mul, Module.End.mul_apply, hp, mul_smul, X_smul, Φ_X,
      coe_Λ₀_one_tmul_T N S 𝒪 bZ bO ρ hb hρT g.ℓ g.prime g.not_dvd g.notMem,
      resO_heckeT N r 𝒪 g.ℓ g.prime (not_dvd_mul N S r hr g)]

include hr hb hρT in

theorem annihilator_le (hρ : Function.Injective ρ) :
    Module.annihilator (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg (AuxLevel.Carrier N r 𝒪) ≤
      (AuxLevel.heckeData N r S 𝒪 θ hc).mTheta := by
  intro p hp
  rw [Module.mem_annihilator] at hp

  have hzero : Λ₀ N S 𝒪 bZ bO ρ (Φ N S r 𝒪 θ hc p) = 0 := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    rw [LinearMap.zero_apply, Submodule.coe_zero]
    apply resO_injective N r 𝒪 hr.ne_zero
    rw [resO_Λ₀_Φ N S r hr 𝒪 θ hc bZ bO hb ρ hρT p φ, hp, map_zero]
  have hΦ : Φ N S r 𝒪 θ hc p = 0 :=
    Λ₀_injective N S 𝒪 bZ bO ρ hρ (by rw [hzero, map_zero])
  show (AuxLevel.heckeData N r S 𝒪 θ hc).thetaTilde.toRingHom p = 0
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ← χ₀_comp_Φ N S r 𝒪 θ hc, AlgHom.comp_apply,
    hΦ, map_zero]

include hr in
omit [CharZero 𝒪] in

theorem finite_freeAlg :
    Module.Finite (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg (AuxLevel.Carrier N r 𝒪) := by
  haveI : NeZero (N * r) := ⟨mul_ne_zero (NeZero.ne N) hr.ne_zero⟩
  haveI : Module.Finite 𝒪 (AuxLevel.Carrier N r 𝒪) :=
    CohCarrier.H1_moduleFinite (N * r) (AuxLevel.subgroup N r) 𝒪 𝒪
  exact Module.Finite.of_restrictScalars_finite 𝒪 _ _

include hr in

theorem main : Nontrivial (AuxLevel.ML N r S 𝒪 θ hc) := by
  classical

  obtain ⟨bZ, hbZ⟩ := CohCarrier.exists_basis_parabolicHoms_top_two_mul_finrank N
  obtain ⟨bO, hbO⟩ := hbZ 𝒪
  obtain ⟨-, ρ, hρinj, hρT, -⟩ :=
    CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms N S
  haveI := finite_freeAlg N S r hr 𝒪 θ hc
  have hAnn := annihilator_le N S r hr 𝒪 θ hc bZ bO hbO ρ hρT hρinj
  have hmem : (⟨(AuxLevel.heckeData N r S 𝒪 θ hc).mTheta, inferInstance⟩ :
      PrimeSpectrum (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg) ∈
        Module.support (AuxLevel.heckeData N r S 𝒪 θ hc).FreeAlg (AuxLevel.Carrier N r 𝒪) :=
    Module.mem_support_iff_of_finite.mpr hAnn
  exact Module.mem_support_iff.mp hmem

end FreeAlg

end AuxLevelOccupancy
p2m_reactivate "P2MW.S_CuspForm_AuxLevel_nontrivial_ML_of_prime_not_dvd.AuxLevelOccupancy"

open IsLocalRing in
theorem solution
    (N : ℕ) [NeZero N] (S : Set ℕ) (r : ℕ) (hr : r.Prime) (hrN : ¬ r ∣ N)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (hc : CuspForm.AuxLevel.OpComm N r S 𝒪) :
    Nontrivial (CuspForm.AuxLevel.ML N r S 𝒪 θ hc) :=
  AuxLevelOccupancy.main N S r hr 𝒪 θ hc

end S_CuspForm_AuxLevel_nontrivial_ML_of_prime_not_dvd
end P2MW
export P2MW.S_CuspForm_AuxLevel_nontrivial_ML_of_prime_not_dvd (solution)

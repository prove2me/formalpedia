-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_algEquiv_cornerRing_baseHeckeData_of_not_isEisenstein
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a19c1fb1-9534-5544-99d7-b7dac514fcfd

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_AuxLevelHeckeModuleBase
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms
import Theorems.Thm_CohCarrier_exists_basis_parabolicHoms_top_two_mul_finrank
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_algEquiv_cornerRing_baseHeckeData_of_not_isEisenstein
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
set_option linter.unusedSectionVars false

namespace EscompAnemic

open IharaLemma

section Abstract

variable {𝒪 : Type} [CommRing 𝒪]
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

theorem exists_algHom_comp_eq_res
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Λ : B →ₐ[𝒪] Module.End 𝒪 Vp) (hΛ : Function.Injective Λ)
    (G : Set R) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hgen : ∀ g ∈ G, ∃ b : B, Λ b = res ρV Vp hstab g) :
    ∃ f : R →ₐ[𝒪] B, ∀ r : R, Λ (f r) = res ρV Vp hstab r := by
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
  refine ⟨f, fun r => ?_⟩
  show Λ (eΛ.symm ⟨resA r, hres_mem r⟩) = resA r
  have h := AlgEquiv.ofInjective_apply Λ hΛ (eΛ.symm ⟨resA r, hres_mem r⟩)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

theorem exists_algEquiv_cornerRing
    (hρV : Function.Injective ρV)
    (Sp : IdempotentSplitting R) (i₀ : Fin Sp.n)
    (hcorner : ∀ v : V, ρV (Sp.e i₀) v ∈ Vp)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (𝔫 : Ideal B) [𝔫.IsMaximal]
    (L : Type) [CommRing L] [Algebra B L] [Algebra 𝒪 L] [IsScalarTower 𝒪 B L]
    [IsLocalization.AtPrime L 𝔫]
    (Λ : B →ₐ[𝒪] Module.End 𝒪 Vp) (hΛ : Function.Injective Λ)
    (hsurj : ∀ b : B, ∃ r : R, Λ b = res ρV Vp hstab r)
    {K : Type} [CommRing K] [Algebra 𝒪 K] (χR : R →ₐ[𝒪] K) (χB : B →ₐ[𝒪] K)
    (hχR : ∀ r : R, χR r = 0 ↔ r ∈ Sp.𝔪 i₀) (hχB : ∀ b : B, χB b = 0 ↔ b ∈ 𝔫)
    (f : R →ₐ[𝒪] B) (hΛf : ∀ r : R, Λ (f r) = res ρV Vp hstab r)
    (hχ : ∀ r : R, χB (f r) = χR r) :
    ∃ E : L ≃ₐ[𝒪] Sp.CornerRing i₀,
      ∀ (b : B) (r : R), Λ b = res ρV Vp hstab r → E (algebraMap B L b) = Sp.toCornerRing i₀ r := by
  classical
  set resA := res ρV Vp hstab with hresA
  have hf_of : ∀ b r, Λ b = resA r → f r = b := fun b r h => hΛ (by rw [hΛf, h])
  have hfsurj : Function.Surjective f := fun b => by
    obtain ⟨r, hr⟩ := hsurj b
    exact ⟨r, hf_of b r hr⟩

  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker (Sp.toCornerRing i₀) := by
    intro r hr
    rw [RingHom.mem_ker] at hr ⊢
    have hr' : f r = 0 := hr
    have hres0 : resA r = 0 := by rw [← hΛf, hr', map_zero]
    have hre : r * Sp.e i₀ = 0 := by
      apply hρV
      rw [map_mul, map_zero]
      apply LinearMap.ext
      intro v
      have hv : ρV (Sp.e i₀) v ∈ Vp := hcorner v
      have h := congrArg Subtype.val (LinearMap.congr_fun hres0 ⟨_, hv⟩)
      simpa [hresA] using h
    apply Subtype.ext
    show Sp.e i₀ * r * Sp.e i₀ = ((0 : Sp.CornerRing i₀) : R)
    rw [mul_comm (Sp.e i₀) r, hre, zero_mul]
    rfl

  let τ : B →+* Sp.CornerRing i₀ :=
    (f.toRingHom.liftOfRightInverse (Function.surjInv hfsurj)
      (Function.rightInverse_surjInv hfsurj)) ⟨Sp.toCornerRing i₀, hker⟩
  have hτf : ∀ r, τ (f r) = Sp.toCornerRing i₀ r := fun r =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ r
  letI : Algebra B (Sp.CornerRing i₀) := τ.toAlgebra
  haveI : IsScalarTower 𝒪 B (Sp.CornerRing i₀) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap 𝒪 (Sp.CornerRing i₀) a = τ (algebraMap 𝒪 B a)
      rw [← f.commutes a, hτf]
      rfl

  have hloc : IsLocalization ((Sp.𝔪 i₀).primeCompl.map f.toRingHom) (Sp.CornerRing i₀) :=
    IsLocalization.of_surjective (Sp.𝔪 i₀).primeCompl (Sp.CornerRing i₀) f.toRingHom hfsurj
      (RingHom.id _) Function.surjective_id
      (RingHom.ext fun r => (hτf r).symm)
      (fun x hx => by
        rw [RingHom.mem_ker, RingHom.id_apply] at hx
        rw [hx]; exact zero_mem _)
  have hmon : (Sp.𝔪 i₀).primeCompl.map f.toRingHom = 𝔫.primeCompl := by
    ext b
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : r ∉ Sp.𝔪 i₀ := hr
      show f r ∉ 𝔫
      rw [← hχB, hχ, hχR]
      exact hr'
    · intro hb
      obtain ⟨r, rfl⟩ := hfsurj b
      refine ⟨r, ?_, rfl⟩
      have hb' : f r ∉ 𝔫 := hb
      show r ∉ Sp.𝔪 i₀
      rw [← hχR, ← hχ, hχB]
      exact hb'
  haveI : IsLocalization 𝔫.primeCompl (Sp.CornerRing i₀) := hmon ▸ hloc
  refine ⟨(IsLocalization.algEquiv 𝔫.primeCompl L (Sp.CornerRing i₀)).restrictScalars 𝒪, ?_⟩
  intro b r hbr
  rw [AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  show τ b = _
  rw [← hf_of b r hbr, hτf]

include hstab in

theorem corner_mem_of_notMem
    (Sp : IdempotentSplitting R) (i₀ : Fin Sp.n) (g : R) (a : 𝒪)
    (hg : g - algebraMap 𝒪 R a ∉ Sp.𝔪 i₀)
    (hpar : ∀ w : V, ρV g w - a • w ∈ Vp) (v : V) :
    ρV (Sp.e i₀) v ∈ Vp := by
  obtain ⟨t, ht⟩ := IharaLemma.exists_mul_mul_eq_of_notMem (Sp.idem i₀) (Sp.𝔪 i₀)
    (Sp.mem_of_isMaximal_of_ne i₀) hg
  have hev : ρV (Sp.e i₀) v = ρV t (ρV (g - algebraMap 𝒪 R a) (ρV (Sp.e i₀) v)) := by
    conv_lhs => rw [← ht]
    rw [map_mul, map_mul]
    rfl
  rw [hev]
  apply hstab
  rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, Module.algebraMap_end_apply]
  exact hpar _

theorem notMem_𝔪_of_apply_ne {K : Type} [CommRing K] [Algebra 𝒪 K]
    (Sp : IdempotentSplitting R) (i₀ : Fin Sp.n) (χR : R →ₐ[𝒪] K)
    (hχR : ∀ x : R, χR x = 0 ↔ x ∈ Sp.𝔪 i₀) (g : R) (a : 𝒪)
    (hne : χR g ≠ algebraMap 𝒪 K a) :
    g - algebraMap 𝒪 R a ∉ Sp.𝔪 i₀ := by
  intro hmem
  apply hne
  have h0 : χR (g - algebraMap 𝒪 R a) = 0 := (hχR _).mpr hmem
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h0
  exact h0

theorem exists_point_of_char (Sp : IdempotentSplitting R) {K : Type} [Field K] [Algebra 𝒪 K]
    (hk : Function.Surjective (algebraMap 𝒪 K)) (χR : R →ₐ[𝒪] K) :
    ∃ (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] K),
      (∀ x, χR x = 0 ↔ x ∈ Sp.𝔪 i₀) ∧ ∀ x, πk (Sp.toCornerRing i₀ x) = χR x := by
  classical
  have hχsurj : Function.Surjective χR := fun y => by
    obtain ⟨a, rfl⟩ := hk y
    exact ⟨algebraMap 𝒪 R a, χR.commutes a⟩
  have hmax : (RingHom.ker χR.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective χR.toRingHom hχsurj
  obtain ⟨i₀, hi₀⟩ := Sp.exists_eq _ hmax
  have hmem : ∀ x : R, χR x = 0 ↔ x ∈ Sp.𝔪 i₀ := fun x => by
    rw [hi₀, RingHom.mem_ker]; rfl

  have he1 : χR (Sp.e i₀) = 1 := by
    have hne : χR (Sp.e i₀) ≠ 0 := fun h => Sp.notMem i₀ ((hmem _).mp h)
    have hidem : χR (Sp.e i₀) * χR (Sp.e i₀) = 1 * χR (Sp.e i₀) := by
      rw [← map_mul, (Sp.idem i₀).eq, one_mul]
    exact mul_right_cancel₀ hne hidem

  have hker : RingHom.ker (Sp.toCornerRing i₀) ≤ RingHom.ker χR.toRingHom := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hx' : Sp.e i₀ * x * Sp.e i₀ = 0 := congrArg Subtype.val hx
    show χR x = 0
    have h := congrArg χR hx'
    rw [map_mul, map_mul, he1, one_mul, mul_one, map_zero] at h
    exact h
  have hsurjC : Function.Surjective (Sp.toCornerRing i₀) := fun z => by
    obtain ⟨_, b, rfl⟩ := z
    exact ⟨b, rfl⟩
  let π₀ : Sp.CornerRing i₀ →+* K :=
    (Sp.toCornerRing i₀).liftOfRightInverse (Function.surjInv hsurjC)
      (Function.rightInverse_surjInv hsurjC) ⟨χR.toRingHom, hker⟩
  have hπ₀ : ∀ x, π₀ (Sp.toCornerRing i₀ x) = χR x := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ x
  let πk : Sp.CornerRing i₀ →ₐ[𝒪] K :=
    { π₀ with
      commutes' := fun a => by
        show π₀ (Sp.toCornerRing i₀ (algebraMap 𝒪 R a)) = _
        rw [hπ₀, AlgHom.commutes] }
  exact ⟨i₀, πk, hmem, hπ₀⟩

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
variable (hint : HasIntegralStructure N 2)

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

noncomputable def eBC : (𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) ≃ₐ[𝒪] heckeBaseAlgebra N S 𝒪 :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (latticeBaseChange N S 𝒪)
    ⟨latticeBaseChange_injective N S 𝒪 hint, latticeBaseChange_surjective N S 𝒪⟩)
    fun a => latticeBaseChange_algebraMap N S 𝒪 a

theorem eBC_apply (z : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) :
    eBC N S 𝒪 hint z = latticeBaseChange N S 𝒪 z := rfl

noncomputable def Λ : heckeBaseAlgebra N S 𝒪 →ₐ[𝒪]
    Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :=
  (Λ₀ N S 𝒪 bZ bO ρ).comp (eBC N S 𝒪 hint).symm

theorem Λ_latticeBaseChange (z : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 S)) :
    Λ N S 𝒪 bZ bO ρ hint (latticeBaseChange N S 𝒪 z) = Λ₀ N S 𝒪 bZ bO ρ z := by
  show Λ₀ N S 𝒪 bZ bO ρ ((eBC N S 𝒪 hint).symm (eBC N S 𝒪 hint z)) = _
  rw [AlgEquiv.symm_apply_apply]

theorem Λ_tmul (a : 𝒪) (t : ↥(heckeAlgebra N 2 S)) :
    Λ N S 𝒪 bZ bO ρ hint (latticeBaseChange N S 𝒪 (a ⊗ₜ t)) = a • ιO N 𝒪 bZ bO (ρ t) := by
  rw [Λ_latticeBaseChange, Λ₀_tmul]

theorem Λ_injective [IsDomain 𝒪] [CharZero 𝒪] (hρ : Function.Injective ρ) :
    Function.Injective (Λ N S 𝒪 bZ bO ρ hint) :=
  (Λ₀_injective N S 𝒪 bZ bO ρ hρ).comp (eBC N S 𝒪 hint).symm.injective

theorem Λ_mem_of_generators
    (T' : Subalgebra 𝒪 (Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)))
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      ιO N 𝒪 bZ bO (ρ (heckeAlgebra.T hℓ hℓN hℓS)) ∈ T')
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
      ιO N 𝒪 bZ bO (ρ (heckeAlgebra.U hq hqN hqS)) ∈ T')
    (b : heckeBaseAlgebra N S 𝒪) :
    Λ N S 𝒪 bZ bO ρ hint b ∈ T' := by
  have hall : ∀ t : ↥(heckeAlgebra N 2 S), ιO N 𝒪 bZ bO (ρ t) ∈ T' := by
    rintro ⟨t, ht⟩
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
      · exact hT ℓ hℓ hℓN hℓS
      · exact hU q hq hqN hqS
    | algebraMap n =>
      have h1 : (⟨algebraMap ℤ _ n, Subalgebra.algebraMap_mem _ n⟩ : ↥(heckeAlgebra N 2 S)) =
          algebraMap ℤ ↥(heckeAlgebra N 2 S) n := Subtype.ext rfl
      have h2 : ιO N 𝒪 bZ bO (ρ (algebraMap ℤ ↥(heckeAlgebra N 2 S) n)) =
          algebraMap 𝒪 (Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪))
            (n : 𝒪) :=
        RingHom.congr_fun (RingHom.ext_int
          (((ιO N 𝒪 bZ bO).comp ρ).comp (algebraMap ℤ ↥(heckeAlgebra N 2 S)))
          ((algebraMap 𝒪 (Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪))).comp
            (Int.castRingHom 𝒪))) n
      rw [h1, h2]
      exact T'.algebraMap_mem _
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : ↥(heckeAlgebra N 2 S)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add]
      exact T'.add_mem ihx ihy
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : ↥(heckeAlgebra N 2 S)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul]
      exact T'.mul_mem ihx ihy
  obtain ⟨z, rfl⟩ := latticeBaseChange_surjective N S 𝒪 b
  rw [Λ_latticeBaseChange]
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact T'.zero_mem
  | tmul a t =>
    rw [Λ₀_tmul]
    exact T'.smul_mem (hall t) a
  | add x y hx hy =>
    rw [map_add]
    exact T'.add_mem hx hy

end Lambda

section Concrete

open CohCarrier CuspForm IharaLemma CuspForm.AuxLevel
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable (N : ℕ) [NeZero N] (S : Finset ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (r : ℕ)
variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
variable (θ : ↥(heckeAlgebra N 2 (↑S : Set ℕ)) →+* IsLocalRing.ResidueField 𝒪)
variable (hc₀ : BaseOpComm N r (↑S : Set ℕ) 𝒪)
variable {I : Type} [Fintype I] [DecidableEq I]
variable (bZ : Module.Basis I ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
variable (bO : Module.Basis I 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪))
variable (hb : ∀ i, (bO i : H1 N ⊤ 𝒪) = (Int.castAddHom 𝒪).comp (bZ i : H1 N ⊤ ℤ))
variable (ρ : ↥(heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) →+*
  Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ))
variable (hρT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑(insert r S) : Set ℕ))
    (φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)),
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((ρ (heckeAlgebra.T hℓ hℓN hℓS) φ :
      ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH N ⊤) ℤ)) : H1 N ⊤ ℤ) = heckeT N ⊤ ℓ ℤ φ)

theorem Gen.notMem_insert (g : Gen N r (↑S : Set ℕ)) : g.ℓ ∉ (↑(insert r S) : Set ℕ) :=
  fun h => (Finset.mem_insert.mp h).elim g.ne g.notMem

noncomputable abbrev Tgen (g : Gen N r (↑S : Set ℕ)) : ↥(heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) :=
  heckeAlgebra.T g.prime g.not_dvd (Gen.notMem_insert N S r g)

noncomputable abbrev opGen (g : Gen N r (↑S : Set ℕ)) :
    ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra :=
  ⟨(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩

include hb hρT in
theorem coe_ιO_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑(insert r S) : Set ℕ))
    (φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((ιO N 𝒪 bZ bO (ρ (heckeAlgebra.T hℓ hℓN hℓS)) φ :
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)) : H1 N ⊤ 𝒪) = heckeT N ⊤ ℓ 𝒪 φ :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  coe_ιO_apply_of_heckeT N 𝒪 bZ bO hb ℓ _ (hρT ℓ hℓ hℓN hℓS) φ

theorem op_apply (g : Gen N r (↑S : Set ℕ)) (v : H1 N ⊤ 𝒪) :
    (baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).op g v =
      (haveI : NeZero g.ℓ := ⟨g.prime.ne_zero⟩; heckeT N ⊤ g.ℓ 𝒪 v) := rfl

include hb hρT in
open scoped IsMulCommutative in

theorem stab (x : ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra)
    (v : H1 N ⊤ 𝒪) (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) :
    (x : Module.End 𝒪 (H1 N ⊤ 𝒪)) v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪 := by
  obtain ⟨x, hx⟩ := x
  revert v
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    haveI : NeZero g.ℓ := ⟨g.prime.ne_zero⟩
    show (baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).op g v ∈ _
    rw [op_apply, ← coe_ιO_T N S r 𝒪 bZ bO hb ρ hρT g.ℓ g.prime g.not_dvd
      (Gen.notMem_insert N S r g) ⟨v, hv⟩]
    exact SetLike.coe_mem _
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
    @AlgHom 𝒪 ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra (Module.End 𝒪 (H1 N ⊤ 𝒪)) _
      CommSemiring.toSemiring _ inferInstance _ :=
  (baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra.val

open scoped IsMulCommutative in
theorem valC_apply (x : ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra) (v : H1 N ⊤ 𝒪) :
    valC N S r 𝒪 θ hc₀ x v = (x : Module.End 𝒪 (H1 N ⊤ 𝒪)) v := rfl

open scoped IsMulCommutative in
theorem valC_injective : Function.Injective (valC N S r 𝒪 θ hc₀) :=
  fun _ _ h => Subtype.ext h

include hb hρT in
open scoped IsMulCommutative in

theorem hstab :
    ∀ x : ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra,
      ∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪,
        valC N S r 𝒪 θ hc₀ x v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪 :=
  fun x v hv => stab N S r 𝒪 θ hc₀ bZ bO hb ρ hρT x v hv

variable (hint : HasIntegralStructure N 2)

include hb hρT in
open scoped IsMulCommutative in

theorem Λ_T
    (hst : ∀ x : ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra,
      ∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪,
        valC N S r 𝒪 θ hc₀ x v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)
    (g : Gen N r (↑S : Set ℕ)) :
    Λ N (↑(insert r S) : Set ℕ) 𝒪 bZ bO ρ hint
        (latticeBaseChange N (↑(insert r S) : Set ℕ) 𝒪 (1 ⊗ₜ Tgen N S r g)) =
      res (valC N S r 𝒪 θ hc₀) (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst
        (opGen N S r 𝒪 θ hc₀ g) := by
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rw [Λ_tmul, one_smul, res_apply_coe, valC_apply]
  exact coe_ιO_T N S r 𝒪 bZ bO hb ρ hρT g.ℓ g.prime g.not_dvd (Gen.notMem_insert N S r g) φ

theorem adjoin_generators_eq_top :
    Algebra.adjoin 𝒪 (Subtype.val ⁻¹'
      Set.range (baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).op :
      Set ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra) = ⊤ :=
  Algebra.adjoin_adjoin_coe_preimage

variable (θ' : ↥(heckeAlgebra N 2 (↑(insert r S) : Set ℕ)) →+* IsLocalRing.ResidueField 𝒪)

noncomputable def χB : heckeBaseAlgebra N (↑(insert r S) : Set ℕ) 𝒪 →ₐ[𝒪] IsLocalRing.ResidueField 𝒪 :=
  { (residualCharacter N (↑(insert r S) : Set ℕ) 𝒪 θ').toRingHom.comp
      ((eBC N (↑(insert r S) : Set ℕ) 𝒪 hint).symm :
        heckeBaseAlgebra N (↑(insert r S) : Set ℕ) 𝒪 →ₐ[𝒪]
          𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 (↑(insert r S) : Set ℕ))).toRingHom with
    commutes' := fun a => by
      show residualCharacter N (↑(insert r S) : Set ℕ) 𝒪 θ'
        ((eBC N (↑(insert r S) : Set ℕ) 𝒪 hint).symm (algebraMap 𝒪 _ a)) = _
      rw [← (eBC N (↑(insert r S) : Set ℕ) 𝒪 hint).commutes a, AlgEquiv.symm_apply_apply,
        residualCharacter_algebraMap]
      rfl }

theorem χB_latticeBaseChange (z : 𝒪 ⊗[ℤ] ↥(heckeAlgebra N 2 (↑(insert r S) : Set ℕ))) :
    χB N S r 𝒪 hint θ' (latticeBaseChange N (↑(insert r S) : Set ℕ) 𝒪 z) =
      residualCharacter N (↑(insert r S) : Set ℕ) 𝒪 θ' z := by
  show residualCharacter N (↑(insert r S) : Set ℕ) 𝒪 θ'
    ((eBC N (↑(insert r S) : Set ℕ) 𝒪 hint).symm (eBC N (↑(insert r S) : Set ℕ) 𝒪 hint z)) = _
  rw [AlgEquiv.symm_apply_apply]

theorem χB_eq_zero_iff (b : heckeBaseAlgebra N (↑(insert r S) : Set ℕ) 𝒪) :
    χB N S r 𝒪 hint θ' b = 0 ↔ b ∈ heckeLocalIdeal N (↑(insert r S) : Set ℕ) 𝒪 θ' := by
  obtain ⟨z, rfl⟩ := latticeBaseChange_surjective N (↑(insert r S) : Set ℕ) 𝒪 b
  rw [χB_latticeBaseChange, ← mem_heckeCharKernel_iff, heckeLocalIdeal,
    Ideal.mem_map_iff_of_surjective _ (latticeBaseChange_surjective N (↑(insert r S) : Set ℕ) 𝒪)]
  constructor
  · intro hz; exact ⟨z, hz, rfl⟩
  · rintro ⟨x, hx, hxz⟩
    rwa [← latticeBaseChange_injective N (↑(insert r S) : Set ℕ) 𝒪 hint hxz]

include hb hρT in
open scoped IsMulCommutative in

theorem exists_f
    (hst : ∀ x : ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra,
      ∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪,
        valC N S r 𝒪 θ hc₀ x v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)
    [CharZero 𝒪] (hρinj : Function.Injective ρ) :
    ∃ f : ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra →ₐ[𝒪]
        heckeBaseAlgebra N (↑(insert r S) : Set ℕ) 𝒪,
      (∀ x, Λ N (↑(insert r S) : Set ℕ) 𝒪 bZ bO ρ hint (f x) =
        res (valC N S r 𝒪 θ hc₀) (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst x) ∧
      ∀ g : Gen N r (↑S : Set ℕ), f (opGen N S r 𝒪 θ hc₀ g) =
        latticeBaseChange N (↑(insert r S) : Set ℕ) 𝒪 (1 ⊗ₜ Tgen N S r g) := by
  have hΛ := Λ_injective N (↑(insert r S) : Set ℕ) 𝒪 bZ bO ρ hint hρinj
  have hΛT := Λ_T N S r 𝒪 θ hc₀ bZ bO hb ρ hρT hint hst
  obtain ⟨f, hf⟩ := exists_algHom_comp_eq_res (valC N S r 𝒪 θ hc₀)
    (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst
    (Λ N (↑(insert r S) : Set ℕ) 𝒪 bZ bO ρ hint) hΛ _ (adjoin_generators_eq_top N S r 𝒪 θ hc₀)
    (by
      rintro ⟨x, hxmem⟩ ⟨g, hg⟩
      dsimp only at hg
      subst hg
      exact ⟨_, hΛT g⟩)
  refine ⟨f, hf, fun g => hΛ ?_⟩
  rw [hf, hΛT]

include hb hρT in
open scoped IsMulCommutative in

theorem hcorner
    (Sp : IdempotentSplitting ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra)
    (i₀ : Fin Sp.n) (χR : ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra →ₐ[𝒪]
      IsLocalRing.ResidueField 𝒪)
    (hχR : ∀ x, χR x = 0 ↔ x ∈ Sp.𝔪 i₀)
    (hχRgen : ∀ g : Gen N r (↑S : Set ℕ), χR (opGen N S r 𝒪 θ hc₀ g) =
      θ (heckeAlgebra.T g.prime g.not_dvd g.notMem))
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ℓ ≠ r ∧ ℓ ≡ 1 [MOD N] ∧
        θ (heckeAlgebra.T hℓ hℓN hℓS) ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1)
    (v : H1 N ⊤ 𝒪) :
    valC N S r 𝒪 θ hc₀ (Sp.e i₀) v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪 := by
  obtain ⟨ℓ₀, hℓ₀, hℓ₀N, hℓ₀S, hℓ₀r, hmod, hne⟩ := hEis
  haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩
  let g₀ : Gen N r (↑S : Set ℕ) := ⟨ℓ₀, hℓ₀, hℓ₀S, hℓ₀N, hℓ₀r⟩
  refine corner_mem_of_notMem (valC N S r 𝒪 θ hc₀)
    (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪)
    (hstab N S r 𝒪 θ hc₀ bZ bO hb ρ hρT) Sp i₀ (opGen N S r 𝒪 θ hc₀ g₀) ((ℓ₀ : 𝒪) + 1)
    (notMem_𝔪_of_apply_ne Sp i₀ χR hχR _ _ ?_) ?_ v
  · rw [hχRgen, map_add, map_natCast, map_one]
    exact hne
  · intro w
    rw [valC_apply, ← Nat.cast_succ, Nat.cast_smul_eq_nsmul]
    exact CohCarrier.heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one N 𝒪 w ℓ₀ hℓ₀ hℓ₀N
      (fun t ht => hmod.of_dvd ((Dvd.intro _ rfl : t ∣ t * t).trans ht))

end Concrete

section Final

open CohCarrier CuspForm IharaLemma CuspForm.AuxLevel
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open scoped IsMulCommutative in
theorem main
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (r : ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra N 2 (↑(insert r S) : Set ℕ) →+* IsLocalRing.ResidueField 𝒪)
    (hθ' : ∀ t : CuspForm.heckeAlgebra N 2 (↑(insert r S) : Set ℕ),
      θ' t = θ (Subalgebra.inclusion
        (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr (Finset.subset_insert r S))) t))
    (hc₀ : CuspForm.AuxLevel.BaseOpComm N r (↑S : Set ℕ) 𝒪)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ℓ ≠ r ∧ ℓ ≡ 1 [MOD N] ∧
        θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CuspForm.AuxLevel.baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra) :
    ∃ (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪),
      (∀ g : CuspForm.AuxLevel.Gen N r (↑S : Set ℕ),
        πk (Sp.toCornerRing i₀ (opGen N S r 𝒪 θ hc₀ g)) =
          θ (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem)) ∧
      ∃ e : CuspForm.heckeLocal N (↑(insert r S) : Set ℕ) 𝒪 θ' ≃ₐ[𝒪] Sp.CornerRing i₀,
        ∀ g : CuspForm.AuxLevel.Gen N r (↑S : Set ℕ),
          e (CuspForm.heckeLocal.π N (↑(insert r S) : Set ℕ) 𝒪 θ' (Tgen N S r g)) =
            Sp.toCornerRing i₀ (opGen N S r 𝒪 θ hc₀ g) := by
  classical
  have hint : HasIntegralStructure N 2 := Fact.out

  obtain ⟨bZ, hbZ⟩ := CohCarrier.exists_basis_parabolicHoms_top_two_mul_finrank N
  obtain ⟨bO, hbO⟩ := hbZ 𝒪
  obtain ⟨-, ρ, hρinj, hρT, -⟩ :=
    CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms N (↑(insert r S) : Set ℕ)

  have hst := hstab N S r 𝒪 θ hc₀ bZ bO hbO ρ hρT
  have hΛ := Λ_injective N (↑(insert r S) : Set ℕ) 𝒪 bZ bO ρ hint hρinj
  have hΛT := Λ_T N S r 𝒪 θ hc₀ bZ bO hbO ρ hρT hint hst

  obtain ⟨f, hf, hfgen⟩ := exists_f N S r 𝒪 θ hc₀ bZ bO hbO ρ hρT hint hst hρinj

  set χR : ↥(baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra →ₐ[𝒪]
      IsLocalRing.ResidueField 𝒪 := (χB N S r 𝒪 hint θ').comp f with hχRdef
  have hχRgen : ∀ g : Gen N r (↑S : Set ℕ), χR (opGen N S r 𝒪 θ hc₀ g) =
      θ (heckeAlgebra.T g.prime g.not_dvd g.notMem) := by
    intro g
    rw [hχRdef, AlgHom.comp_apply, hfgen, χB_latticeBaseChange, residualCharacter_tmul, map_one,
      one_mul, hθ']
    rfl
  have hk : Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField 𝒪)) :=
    Ideal.Quotient.mk_surjective
  obtain ⟨i₀, πk, hχR, hπk⟩ := exists_point_of_char Sp hk χR

  have hcor := hcorner N S r 𝒪 θ hc₀ bZ bO hbO ρ hρT Sp i₀ χR hχR hχRgen hEis

  have hsurj : ∀ x, ∃ y, Λ N (↑(insert r S) : Set ℕ) 𝒪 bZ bO ρ hint x =
      res (valC N S r 𝒪 θ hc₀) (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst y := by
    intro x
    have hx := Λ_mem_of_generators N (↑(insert r S) : Set ℕ) 𝒪 bZ bO ρ hint
      (res (valC N S r 𝒪 θ hc₀) (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst).range
      ?_ ?_ x
    · obtain ⟨y, hy⟩ := hx
      exact ⟨y, hy.symm⟩
    · intro ℓ hℓ hℓN hℓS
      have hℓS₀ : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS (by
        rw [Finset.coe_insert]; exact Set.mem_insert_of_mem _ h)
      have hℓr : ℓ ≠ r := fun h => hℓS (by
        rw [Finset.coe_insert, h]; exact Set.mem_insert _ _)
      let g : Gen N r (↑S : Set ℕ) := ⟨ℓ, hℓ, hℓS₀, hℓN, hℓr⟩
      refine ⟨opGen N S r 𝒪 θ hc₀ g, ?_⟩
      show res _ _ hst _ = _
      rw [← hΛT g, Λ_tmul, one_smul]
    · intro q hq hqN hqS
      exact absurd (show q ∈ (↑(insert r S) : Set ℕ) by
        rw [Finset.coe_insert]; exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr (hNS q hq hqN))) hqS
  have hχB := χB_eq_zero_iff N S r 𝒪 hint θ'
  obtain ⟨E, hE⟩ := exists_algEquiv_cornerRing
    (valC N S r 𝒪 θ hc₀) (ModularCurve.Period.parabolicHoms 𝒪 (GammaH N ⊤) 𝒪) hst
    (valC_injective N S r 𝒪 θ hc₀) Sp i₀ hcor
    (heckeLocalIdeal N (↑(insert r S) : Set ℕ) 𝒪 θ') (heckeLocal N (↑(insert r S) : Set ℕ) 𝒪 θ')
    (Λ N (↑(insert r S) : Set ℕ) 𝒪 bZ bO ρ hint) hΛ hsurj
    χR (χB N S r 𝒪 hint θ') hχR hχB f hf (fun _ => rfl)
  refine ⟨i₀, πk, fun g => ?_, E, fun g => ?_⟩
  · rw [hπk, hχRgen]
  · exact hE _ _ (hΛT g)

end Final

end EscompAnemic
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_exists_algEquiv_cornerRing_baseHeckeData_of_not_isEisenstein.EscompAnemic"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
open scoped IsMulCommutative in
theorem solution
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (r : ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra N 2 (↑(insert r S) : Set ℕ) →+* IsLocalRing.ResidueField 𝒪)
    (hθ' : ∀ t : CuspForm.heckeAlgebra N 2 (↑(insert r S) : Set ℕ),
      θ' t = θ (Subalgebra.inclusion
        (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr (Finset.subset_insert r S))) t))
    (hc₀ : CuspForm.AuxLevel.BaseOpComm N r (↑S : Set ℕ) 𝒪)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ℓ ≠ r ∧ ℓ ≡ 1 [MOD N] ∧
        θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CuspForm.AuxLevel.baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).opSubalgebra) :
    ∃ (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪),
      (∀ g : CuspForm.AuxLevel.Gen N r (↑S : Set ℕ),
        πk (Sp.toCornerRing i₀
          ⟨(CuspForm.AuxLevel.baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).op g,
            Algebra.subset_adjoin (Set.mem_range_self g)⟩) =
          θ (CuspForm.heckeAlgebra.T g.prime g.not_dvd g.notMem)) ∧
      ∃ e : CuspForm.heckeLocal N (↑(insert r S) : Set ℕ) 𝒪 θ' ≃ₐ[𝒪] Sp.CornerRing i₀,
        ∀ g : CuspForm.AuxLevel.Gen N r (↑S : Set ℕ),
          e (CuspForm.heckeLocal.π N (↑(insert r S) : Set ℕ) 𝒪 θ'
              (CuspForm.heckeAlgebra.T g.prime g.not_dvd
                (fun h => (Finset.mem_insert.mp h).elim g.ne g.notMem))) =
            Sp.toCornerRing i₀
              ⟨(CuspForm.AuxLevel.baseHeckeData N r (↑S : Set ℕ) 𝒪 θ hc₀).op g,
                Algebra.subset_adjoin (Set.mem_range_self g)⟩ :=
  EscompAnemic.main N S hNS r 𝒪 θ θ' hθ' hc₀ hEis Sp

end S_CuspForm_heckeLocal_exists_algEquiv_cornerRing_baseHeckeData_of_not_isEisenstein
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_algEquiv_cornerRing_baseHeckeData_of_not_isEisenstein (solution)

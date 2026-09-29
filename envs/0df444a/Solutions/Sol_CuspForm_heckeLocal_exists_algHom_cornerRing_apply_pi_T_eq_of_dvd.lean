-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_algHom_cornerRing_apply_pi_T_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/68258bfb-ed42-598b-b104-7da04a517030

import Definitions.Def_CuspForm_HeckeModuleCornerRealization
import Theorems.Thm_CohCarrier_exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_CuspForm_heckeAlgebra_exists_surjective_ringHom_of_dvd
import Theorems.Thm_CuspForm_heckeLocal_exists_factor_algHom
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_algHom_cornerRing_apply_pi_T_eq_of_dvd
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

namespace EsRingRoad

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

include hstab in

theorem exists_ringHom_range_toCornerRing
    (hρV : Function.Injective ρV)
    (Sp : IdempotentSplitting R) (i₀ : Fin Sp.n)
    (hcorner : ∀ v : V, ρV (Sp.e i₀) v ∈ Vp) :
    ∃ (A : Subring (Module.End 𝒪 Vp)) (hA : ∀ r : R, res ρV Vp hstab r ∈ A)
      (τ : ↥A →+* Sp.CornerRing i₀),
      ∀ r : R, τ ⟨res ρV Vp hstab r, hA r⟩ = Sp.toCornerRing i₀ r := by
  classical
  refine ⟨(res ρV Vp hstab).toRingHom.range, fun r => RingHom.mem_range_self _ r, ?_⟩
  set resA := res ρV Vp hstab with hresA
  let f : R →+* ↥resA.toRingHom.range := resA.toRingHom.rangeRestrict
  have hfsurj : Function.Surjective f := RingHom.rangeRestrict_surjective _
  have hker : RingHom.ker f ≤ RingHom.ker (Sp.toCornerRing i₀) := by
    intro r hr
    rw [RingHom.mem_ker] at hr ⊢
    have hres0 : resA r = 0 := congrArg Subtype.val hr
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
  refine ⟨(f.liftOfRightInverse (Function.surjInv hfsurj) (Function.rightInverse_surjInv hfsurj))
    ⟨Sp.toCornerRing i₀, hker⟩, fun r => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply f _ _ _ r

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

variable (M : ℕ)

def castPar (Rr A : Type) [Semiring Rr] [AddCommGroup A] [Module Rr A] (c : ℤ →+ A) :
    ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ) →+
      ↥(ModularCurve.Period.parabolicHoms Rr (GammaH M ⊤) A) where
  toFun φ := ⟨c.comp (φ : H1 M ⊤ ℤ), fun γ hγ => by
    show c ((φ : H1 M ⊤ ℤ) (Additive.ofMul γ)) = 0
    rw [φ.2 γ hγ, map_zero]⟩
  map_zero' := by apply Subtype.ext; ext γ; simp
  map_add' φ ψ := by apply Subtype.ext; ext γ; simp

@[scoped simp] theorem coe_castPar (Rr A : Type) [Semiring Rr] [AddCommGroup A] [Module Rr A] (c : ℤ →+ A)
    (φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ)) :
    ((castPar M Rr A c φ : ↥(ModularCurve.Period.parabolicHoms Rr (GammaH M ⊤) A)) : H1 M ⊤ A) =
      c.comp (φ : H1 M ⊤ ℤ) := rfl

theorem diamondL_top_apply [NeZero M] (𝒪 : Type) [CommRing 𝒪] (d : (ZMod M)ˣ) (φ : H1 M ⊤ 𝒪) :
    diamondL M ⊤ 𝒪 d φ = φ := by
  show diamondRaw M ⊤ 𝒪 (Classical.choose (gamma0Units_surjective M d)) φ = φ
  set σ := Classical.choose (gamma0Units_surjective M d)
  have hσ : (σ : SL(2, ℤ)) ∈ GammaH M ⊤ := by rw [GammaH_top]; exact σ.2
  ext γ
  show φ (Additive.ofMul (conjHom M ⊤ σ (Additive.toMul γ))) = φ γ
  have hconj : conjHom M ⊤ σ (Additive.toMul γ) =
      ⟨σ, hσ⟩ * Additive.toMul γ * ⟨σ, hσ⟩⁻¹ := Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  simp

end Furniture

section BaseChange

open CohCarrier

variable (M : ℕ) (𝒪 : Type) [CommRing 𝒪]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (bZ : Module.Basis I ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ))
variable (bO : Module.Basis I 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪))
variable (hb : ∀ i, (bO i : H1 M ⊤ 𝒪) = (Int.castAddHom 𝒪).comp (bZ i : H1 M ⊤ ℤ))

noncomputable def ιO : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ) →+*
    Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪) :=
  (Matrix.toLinAlgEquiv bO).toRingEquiv.toRingHom.comp
    ((Int.castRingHom 𝒪).mapMatrix.comp (LinearMap.toMatrixAlgEquiv bZ).toRingEquiv.toRingHom)

theorem ιO_apply (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ)) :
    ιO M 𝒪 bZ bO f =
      Matrix.toLinAlgEquiv bO ((LinearMap.toMatrixAlgEquiv bZ f).map (Int.castRingHom 𝒪)) := rfl

theorem ιO_apply_basis (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ))
    (j : I) :
    ιO M 𝒪 bZ bO f (bO j) = ∑ i, ((LinearMap.toMatrixAlgEquiv bZ f i j : ℤ) : 𝒪) • bO i := by
  rw [ιO_apply, Matrix.toLinAlgEquiv_self]
  rfl

include hb in
omit [Fintype I] [DecidableEq I] in
theorem castPar_basis (i : I) : castPar M 𝒪 𝒪 (Int.castAddHom 𝒪) (bZ i) = bO i :=
  Subtype.ext (hb i).symm

include hb in

theorem ιO_castPar (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ))
    (x : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ)) :
    ιO M 𝒪 bZ bO f (castPar M 𝒪 𝒪 (Int.castAddHom 𝒪) x) =
      castPar M 𝒪 𝒪 (Int.castAddHom 𝒪) (f x) := by

  set c := castPar M 𝒪 𝒪 (Int.castAddHom 𝒪) with hc
  let G₁ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ) →ₗ[ℤ]
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪) :=
    ((ιO M 𝒪 bZ bO f).toAddMonoidHom.comp c).toIntLinearMap
  let G₂ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ) →ₗ[ℤ]
      ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪) :=
    (c.comp f.toAddMonoidHom).toIntLinearMap
  suffices h : G₁ = G₂ from LinearMap.congr_fun h x
  apply bZ.ext
  intro j
  show ιO M 𝒪 bZ bO f (c (bZ j)) = c (f (bZ j))
  rw [hc, castPar_basis M 𝒪 bZ bO hb, ιO_apply_basis]
  conv_rhs => rw [← bZ.sum_repr (f (bZ j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, castPar_basis M 𝒪 bZ bO hb, LinearMap.toMatrixAlgEquiv_apply]
  exact Int.cast_smul_eq_zsmul 𝒪 (M := ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪)) _ _

include hb in

theorem coe_ιO_apply_of_heckeT (n : ℕ) [NeZero n]
    (f : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ))
    (hf : ∀ φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ),
      ((f φ : ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ)) : H1 M ⊤ ℤ) =
        heckeT M ⊤ n ℤ (φ : H1 M ⊤ ℤ))
    (φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪)) :
    ((ιO M 𝒪 bZ bO f φ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪)) : H1 M ⊤ 𝒪) =
      heckeT M ⊤ n 𝒪 (φ : H1 M ⊤ 𝒪) := by
  let F₁ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪) →ₗ[𝒪] H1 M ⊤ 𝒪 :=
    (Submodule.subtype _) ∘ₗ (ιO M 𝒪 bZ bO f)
  let F₂ : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪) →ₗ[𝒪] H1 M ⊤ 𝒪 :=
    (heckeTL M ⊤ 𝒪 n) ∘ₗ (Submodule.subtype _)
  suffices h : F₁ = F₂ from LinearMap.congr_fun h φ
  apply bO.ext
  intro i
  show ((ιO M 𝒪 bZ bO f (bO i) : ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪)) :
      H1 M ⊤ 𝒪) = heckeT M ⊤ n 𝒪 (bO i : H1 M ⊤ 𝒪)
  rw [← castPar_basis M 𝒪 bZ bO hb i, ιO_castPar M 𝒪 bZ bO hb, coe_castPar, hf, coe_castPar,
    heckeT_comp]

include hb in

theorem heckeT_mem_parabolicHoms
    (hB1 : ∀ (n : ℕ) [NeZero n] (φ : H1 M ⊤ ℤ),
      φ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ →
        heckeT M ⊤ n ℤ φ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ)
    (n : ℕ) [NeZero n] (v : H1 M ⊤ 𝒪)
    (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪) :
    heckeT M ⊤ n 𝒪 v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪 := by
  let fZ : Module.End ℤ ↥(ModularCurve.Period.parabolicHoms ℤ (GammaH M ⊤) ℤ) :=
    ((heckeT M ⊤ n ℤ).toIntLinearMap).restrict (fun φ hφ => hB1 n φ hφ)
  have h := coe_ιO_apply_of_heckeT M 𝒪 bZ bO hb n fZ (fun φ => rfl) ⟨v, hv⟩
  rw [← h]
  exact SetLike.coe_mem _

end BaseChange

section Concrete

open CohCarrier CuspForm

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable (L : ℕ) [NeZero L] (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]
variable (hcomm : ∀ g h : Gen L S,
  opFamily L ⊤ S 𝒪 g * opFamily L ⊤ S 𝒪 h = opFamily L ⊤ S 𝒪 h * opFamily L ⊤ S 𝒪 g)
variable (θbar : Gen L S → k)

open scoped IsMulCommutative in

noncomputable def valC :
    @AlgHom 𝒪 ↥(hdata L ⊤ S 𝒪 k hcomm θbar).opSubalgebra (Module.End 𝒪 (H1 L ⊤ 𝒪)) _
      CommSemiring.toSemiring _ inferInstance _ :=
  (hdata L ⊤ S 𝒪 k hcomm θbar).opSubalgebra.val

open scoped IsMulCommutative in
theorem valC_apply (r : ↥(hdata L ⊤ S 𝒪 k hcomm θbar).opSubalgebra) (v : H1 L ⊤ 𝒪) :
    valC L S 𝒪 k hcomm θbar r v = (r : Module.End 𝒪 (H1 L ⊤ 𝒪)) v := rfl

open scoped IsMulCommutative in
theorem valC_injective : Function.Injective (valC L S 𝒪 k hcomm θbar) :=
  fun _ _ h => Subtype.ext h

open scoped IsMulCommutative in

theorem stab
    (hT : ∀ (n : ℕ) [NeZero n] (v : H1 L ⊤ 𝒪),
      v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪 →
        heckeT L ⊤ n 𝒪 v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪)
    (r : ↥(hdata L ⊤ S 𝒪 k hcomm θbar).opSubalgebra)
    (v : H1 L ⊤ 𝒪) (hv : v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪) :
    valC L S 𝒪 k hcomm θbar r v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪 := by
  rw [valC_apply]
  obtain ⟨x, hx⟩ := r
  revert v
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    cases g with
    | T ℓ hℓ hℓS hℓN =>
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      show heckeT L ⊤ ℓ 𝒪 v ∈ _
      exact hT ℓ v hv
    | U q hq hqN =>
      haveI : NeZero q := ⟨hq.ne_zero⟩
      show heckeT L ⊤ q 𝒪 v ∈ _
      exact hT q v hv
    | dia d =>
      show diamondL L ⊤ 𝒪 d v ∈ _
      rw [diamondL_top_apply]
      exact hv
  | algebraMap a =>
    intro v hv
    show (algebraMap 𝒪 (Module.End 𝒪 (H1 L ⊤ 𝒪)) a) v ∈ _
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ a hv
  | add x y hx hy ihx ihy =>
    intro v hv
    exact Submodule.add_mem _ (ihx v hv) (ihy v hv)
  | mul x y hx hy ihx ihy =>
    intro v hv
    exact ihx _ (ihy v hv)

end Concrete

section HeckeExt

open CuspForm

variable {N : ℕ} [NeZero N] {S : Set ℕ}

set_option synthInstance.maxHeartbeats 800000 in

theorem ringHom_ext {A : Type} [Ring A] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (φ ψ : heckeAlgebra N 2 S →+* A)
    (h : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      φ (heckeAlgebra.T hℓ hℓN hℓS) = ψ (heckeAlgebra.T hℓ hℓN hℓS)) :
    φ = ψ := by
  refine RingHom.ext fun t => ?_
  obtain ⟨t, ht⟩ := t
  refine Algebra.adjoin_induction (p := fun t ht => φ ⟨t, ht⟩ = ψ ⟨t, ht⟩) ?_ ?_ ?_ ?_ ht
  · rintro t (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
    · exact h ℓ hℓ hℓN hℓS
    · exact absurd (hNS q hq hqN) hqS
  · intro r
    have e : (⟨algebraMap ℤ _ r, algebraMap_mem _ r⟩ : heckeAlgebra N 2 S) = (r : heckeAlgebra N 2 S) :=
      Subtype.ext (by simp)
    rw [e, map_intCast φ r, map_intCast ψ r]
  · intro x y hx hy hpx hpy
    have ex : (⟨x + y, add_mem hx hy⟩ : heckeAlgebra N 2 S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [ex, φ.map_add, ψ.map_add, hpx, hpy]
  · intro x y hx hy hpx hpy
    have ex : (⟨x * y, mul_mem hx hy⟩ : heckeAlgebra N 2 S) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [ex, φ.map_mul, ψ.map_mul, hpx, hpy]

end HeckeExt

section Final

open CohCarrier CuspForm IsLocalRing

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open scoped IsMulCommutative in
theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (N L : ℕ) [NeZero N] [NeZero L] (S : Set ℕ) (hLN : L ∣ N)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (hcomm : ∀ g h : CohCarrier.Gen L S,
      CohCarrier.opFamily L ⊤ S 𝒪 g * CohCarrier.opFamily L ⊤ S 𝒪 h =
        CohCarrier.opFamily L ⊤ S 𝒪 h * CohCarrier.opFamily L ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen L S → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen L S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N),
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓL) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    (hpar : ∀ v : CohCarrier.H1 L ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH L ⊤) 𝒪) :
    ∃ φ : CuspForm.heckeLocal N S 𝒪 θ →ₐ[𝒪] Sp.CornerRing i₀,
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N),
        φ (CuspForm.heckeLocal.π N S 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) =
          Sp.toCornerRing i₀
            ⟨(CohCarrier.hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓL),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ := by
  classical
  have hint : HasIntegralStructure N 2 := Fact.out

  letI iT : CommRing ↥(hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra := inferInstance
  letI iNU : NonUnitalCommRing ↥(hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra :=
    inferInstance
  letI iCR : CommRing (Sp.CornerRing i₀) := inferInstance

  haveI : (GammaH L ⊤).FiniteIndex := by rw [GammaH_top]; infer_instance
  obtain ⟨n, bZ, hbR⟩ :=
    ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree (GammaH L ⊤)
  obtain ⟨bO, hbO⟩ := hbR 𝒪

  obtain ⟨hB1, ρ, -, hρT, -⟩ :=
    CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms L S

  obtain ⟨resNL, -, hresT, -⟩ :=
    CuspForm.heckeAlgebra.exists_surjective_ringHom_of_dvd L N hLN 2 S hNS

  have hT : ∀ (m : ℕ) [NeZero m] (v : H1 L ⊤ 𝒪),
      v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪 →
        heckeT L ⊤ m 𝒪 v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪 :=
    fun m _ v hv => heckeT_mem_parabolicHoms L 𝒪 bZ bO hbO hB1 m v hv
  have hst : ∀ r, ∀ v ∈ ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪,
      valC L S 𝒪 (ResidueField 𝒪) hcomm θbar r v ∈
        ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪 :=
    fun r v hv => stab L S 𝒪 (ResidueField 𝒪) hcomm θbar hT r v hv
  have hcor : ∀ v : H1 L ⊤ 𝒪, valC L S 𝒪 (ResidueField 𝒪) hcomm θbar (Sp.e i₀) v ∈
      ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪 :=
    fun v => hpar _ ⟨v, rfl⟩

  obtain ⟨A, hA, τ, hτ⟩ := exists_ringHom_range_toCornerRing
    (valC L S 𝒪 (ResidueField 𝒪) hcomm θbar)
    (ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪) hst
    (valC_injective L S 𝒪 (ResidueField 𝒪) hcomm θbar) Sp i₀ hcor

  let σ : heckeAlgebra N 2 S →+*
      Module.End 𝒪 ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪) :=
    (ιO L 𝒪 bZ bO).comp (ρ.comp resNL)
  have hσT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N),
      σ (heckeAlgebra.T hℓ hℓN hℓS) =
        res (valC L S 𝒪 (ResidueField 𝒪) hcomm θbar)
          (ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪) hst
          ⟨(hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).op (Gen.T ℓ hℓ hℓS hℓL),
            Algebra.subset_adjoin (Set.mem_range_self _)⟩ := by
    intro ℓ hℓ hℓS hℓL hℓN
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    show ((ιO L 𝒪 bZ bO (ρ (resNL (heckeAlgebra.T hℓ hℓN hℓS))) φ :
        ↥(ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪)) : H1 L ⊤ 𝒪) =
      heckeT L ⊤ ℓ 𝒪 (φ : H1 L ⊤ 𝒪)
    rw [hresT ℓ hℓ hℓN hℓL hℓS]
    exact coe_ιO_apply_of_heckeT L 𝒪 bZ bO hbO ℓ _ (hρT ℓ hℓ hℓL hℓS) φ

  have hσmem : ∀ t : heckeAlgebra N 2 S, σ t ∈ A := by
    intro t
    obtain ⟨t, ht⟩ := t
    refine Algebra.adjoin_induction (p := fun t ht => σ ⟨t, ht⟩ ∈ A) ?_ ?_ ?_ ?_ ht
    · rintro t (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
      · have hℓL : ¬ ℓ ∣ L := fun hd => hℓN (hd.trans hLN)
        have hmem : σ (heckeAlgebra.T hℓ hℓN hℓS) ∈ A := by
          rw [hσT ℓ hℓ hℓS hℓL hℓN]
          exact hA _
        exact hmem
      · exact absurd (hNS q hq hqN) hqS
    · intro r
      have e : (⟨algebraMap ℤ _ r, algebraMap_mem _ r⟩ : heckeAlgebra N 2 S) =
          (r : heckeAlgebra N 2 S) := Subtype.ext (by simp)
      rw [e, map_intCast]
      exact intCast_mem A r
    · intro x y hx hy hpx hpy
      have ex : (⟨x + y, add_mem hx hy⟩ : heckeAlgebra N 2 S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [ex, map_add]
      exact add_mem hpx hpy
    · intro x y hx hy hpx hpy
      have ex : (⟨x * y, mul_mem hx hy⟩ : heckeAlgebra N 2 S) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [ex, map_mul]
      exact mul_mem hpx hpy

  let π' : heckeAlgebra N 2 S →+* Sp.CornerRing i₀ := τ.comp (σ.codRestrict A hσmem)
  have hπ'T : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N),
      π' (heckeAlgebra.T hℓ hℓN hℓS) =
        Sp.toCornerRing i₀ ⟨(hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).op (Gen.T ℓ hℓ hℓS hℓL),
          Algebra.subset_adjoin (Set.mem_range_self _)⟩ := by
    intro ℓ hℓ hℓS hℓL hℓN
    show τ ⟨σ (heckeAlgebra.T hℓ hℓN hℓS), hσmem _⟩ = _
    have hx : (⟨σ (heckeAlgebra.T hℓ hℓN hℓS), hσmem _⟩ : ↥A) =
        ⟨res (valC L S 𝒪 (ResidueField 𝒪) hcomm θbar)
            (ModularCurve.Period.parabolicHoms 𝒪 (GammaH L ⊤) 𝒪) hst
            ⟨(hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).op (Gen.T ℓ hℓ hℓS hℓL),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩, hA _⟩ :=
      Subtype.ext (hσT ℓ hℓ hℓS hℓL hℓN)
    rw [hx, hτ]

  have hk : Function.Surjective (algebraMap 𝒪 (ResidueField 𝒪)) := Ideal.Quotient.mk_surjective
  have hχ : ∀ t, πk (π' t) = θ t := by
    have heq := ringHom_ext hNS (πk.toRingHom.comp π') θ fun ℓ hℓ hℓN hℓS => by
      have hℓL : ¬ ℓ ∣ L := fun hd => hℓN (hd.trans hLN)
      show πk (π' (heckeAlgebra.T hℓ hℓN hℓS)) = _
      rw [hπ'T ℓ hℓ hℓS hℓL hℓN, hπk, hθT ℓ hℓ hℓS hℓL hℓN]
    intro t
    exact congrArg (fun f : heckeAlgebra N 2 S →+* ResidueField 𝒪 => f t) heq

  have hπksurj : Function.Surjective πk := fun y => by
    obtain ⟨a, rfl⟩ := hk y
    exact ⟨algebraMap 𝒪 (Sp.CornerRing i₀) a, πk.commutes a⟩
  have hker : RingHom.ker πk.toRingHom = maximalIdeal (Sp.CornerRing i₀) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective πk.toRingHom hπksurj)
  have hmem_max : ∀ z : Sp.CornerRing i₀, z ∈ maximalIdeal (Sp.CornerRing i₀) ↔ πk z = 0 := by
    intro z
    rw [← hker, RingHom.mem_ker]
    rfl
  haveI : IsLocalHom (algebraMap 𝒪 (Sp.CornerRing i₀)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : a ∈ maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal a).mpr hna
    have hz : algebraMap 𝒪 (Sp.CornerRing i₀) a ∈ maximalIdeal (Sp.CornerRing i₀) := by
      rw [hmem_max, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq,
        IsLocalRing.residue_eq_zero_iff]
      exact hmem
    exact (IsLocalRing.notMem_maximalIdeal.mpr ha) hz

  have hπ' : ∀ t, IsLocalRing.residue (Sp.CornerRing i₀) (π' t) =
      IsLocalRing.ResidueField.map (algebraMap 𝒪 (Sp.CornerRing i₀)) (θ t) := by
    intro t
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (θ t)
    rw [← ha, IsLocalRing.ResidueField.map_residue, IsLocalRing.residue_def,
      IsLocalRing.residue_def]
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
    rw [hmem_max]
    have h1 : πk (π' t - algebraMap 𝒪 (Sp.CornerRing i₀) a) =
        πk (π' t) - πk (algebraMap 𝒪 (Sp.CornerRing i₀) a) := map_sub πk _ _
    rw [h1, hχ, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha, sub_self]

  obtain ⟨f, -, hf⟩ :=
    CuspForm.heckeLocal.exists_factor_algHom N S 𝒪 θ hint (Sp.CornerRing i₀) π' hπ'
  exact ⟨f, fun ℓ hℓ hℓS hℓL hℓN => by rw [hf, hπ'T ℓ hℓ hℓS hℓL hℓN]⟩

end Final

end EsRingRoad
p2m_reactivate "P2MW.S_CuspForm_heckeLocal_exists_algHom_cornerRing_apply_pi_T_eq_of_dvd.EsRingRoad"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open IsLocalRing in
open scoped IsMulCommutative in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (N L : ℕ) [NeZero N] [NeZero L] (S : Set ℕ) (hLN : L ∣ N)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ : CuspForm.heckeAlgebra N 2 S →+* ResidueField 𝒪)
    (hcomm : ∀ g h : CohCarrier.Gen L S,
      CohCarrier.opFamily L ⊤ S 𝒪 g * CohCarrier.opFamily L ⊤ S 𝒪 h =
        CohCarrier.opFamily L ⊤ S 𝒪 h * CohCarrier.opFamily L ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen L S → ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n)
    (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen L S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N),
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓL) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    (hpar : ∀ v : CohCarrier.H1 L ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH L ⊤) 𝒪) :
    ∃ φ : CuspForm.heckeLocal N S 𝒪 θ →ₐ[𝒪] Sp.CornerRing i₀,
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓL : ¬ ℓ ∣ L) (hℓN : ¬ ℓ ∣ N),
        φ (CuspForm.heckeLocal.π N S 𝒪 θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) =
          Sp.toCornerRing i₀
            ⟨(CohCarrier.hdata L ⊤ S 𝒪 (ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.T ℓ hℓ hℓS hℓL),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ :=
  EsRingRoad.main N L S hLN hNS θ hcomm θbar Sp i₀ πk hπk hθT hpar

end S_CuspForm_heckeLocal_exists_algHom_cornerRing_apply_pi_T_eq_of_dvd
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_algHom_cornerRing_apply_pi_T_eq_of_dvd (solution)

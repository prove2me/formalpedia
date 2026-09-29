-- Prove2me | solution 1 for CuspForm.linearIndependent_complex_of_linearIndependent_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/cfec112d-9af6-5fbb-bc9a-c3e0746fb9a8

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_ModularCurve_PeriodHomPair
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_HeckeAlgebraHom
import Theorems.Thm_ModularCurve_periodHomPair_range_eq_parabolicHoms
import Theorems.Thm_ModularCurve_Period_charInvolution_heckeOperatorHom
import Theorems.Thm_ModularCurve_periodMap_heckeTLin
import Theorems.Thm_ModularCurve_periodMap_heckeULin
import Theorems.Thm_ModularCurve_periodMap_injective
import Theorems.Thm_ModularCurve_existsPeriodMapLinear
import Theorems.Thm_ModularCurve_periodMap_mem_parabolicHoms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_linearIndependent_complex_of_linearIndependent_int
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000

open Module CongruenceSubgroup ModularCurve ModularCurve.Period

namespace P2mWs11R

theorem heckeOperatorHom_comp {A B : Type*} [AddCommGroup A] [AddCommGroup B] (N ℓ : ℕ) [NeZero ℓ]
    (h : A →+ B) (φ : Additive (Gamma0 N) →+ A) :
    HeckeEis.heckeOperatorHom N ℓ B (h.comp φ) = h.comp (HeckeEis.heckeOperatorHom N ℓ A φ) := by
  refine AddMonoidHom.ext fun γ => ?_
  obtain ⟨g, rfl⟩ : ∃ g, Additive.ofMul g = γ := ⟨Additive.toMul γ, rfl⟩
  rw [HeckeEis.heckeOperatorHom_apply, AddMonoidHom.comp_apply, HeckeEis.heckeOperatorHom_apply,
    map_sum]
  rfl

noncomputable def heckeL (N ℓ : ℕ) [NeZero ℓ] :
    (Additive (Gamma0 N) →+ ℂ) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ) where
  toFun := HeckeEis.heckeOperatorHom N ℓ ℂ
  map_add' := map_add _
  map_smul' c φ := by
    have h1 : ∀ ψ : Additive (Gamma0 N) →+ ℂ, c • ψ = (AddMonoidHom.mulLeft c).comp ψ :=
      fun ψ => AddMonoidHom.ext fun _ => rfl
    rw [RingHom.id_apply, h1, h1, heckeOperatorHom_comp]

@[scoped simp] theorem heckeL_apply (N ℓ : ℕ) [NeZero ℓ] (φ : Additive (Gamma0 N) →+ ℂ) :
    heckeL N ℓ φ = HeckeEis.heckeOperatorHom N ℓ ℂ φ := rfl

section Twin

variable (N : ℕ)

noncomputable def ratToComplex (φq : Additive (Gamma0 N) →+ ℚ) : Additive (Gamma0 N) →+ ℂ :=
  (Rat.castHom ℂ).toAddMonoidHom.comp φq

@[scoped simp] theorem ratToComplex_apply (φq : Additive (Gamma0 N) →+ ℚ) (γ : Additive (Gamma0 N)) :
    ratToComplex N φq γ = ((φq γ : ℚ) : ℂ) := rfl

theorem ratToComplex_add (φ ψ : Additive (Gamma0 N) →+ ℚ) :
    ratToComplex N (φ + ψ) = ratToComplex N φ + ratToComplex N ψ :=
  AddMonoidHom.ext fun _ => by simp

theorem ratToComplex_zsmul (r : ℤ) (φ : Additive (Gamma0 N) →+ ℚ) :
    ratToComplex N (r • φ) = r • ratToComplex N φ :=
  AddMonoidHom.ext fun _ => by simp

def IsTwin (P : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ))
    (t : Module.End ℂ (CuspForm (Gamma0 N) 2))
    (A : (Additive (Gamma0 N) →+ ℂ) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ)) : Prop :=
  (∀ f, P (t f) = A (P f)) ∧
  (∀ φ, A (charInvolution N ℂ ℂ φ) = charInvolution N ℂ ℂ (A φ)) ∧
  (∀ φq : Additive (Gamma0 N) →+ ℚ, ∃ ψq : Additive (Gamma0 N) →+ ℚ,
      A (ratToComplex N φq) = ratToComplex N ψq)

variable {N}

theorem isTwin_add {P : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ)}
    {t₁ t₂ : Module.End ℂ (CuspForm (Gamma0 N) 2)}
    {A₁ A₂ : (Additive (Gamma0 N) →+ ℂ) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ)}
    (h₁ : IsTwin N P t₁ A₁) (h₂ : IsTwin N P t₂ A₂) : IsTwin N P (t₁ + t₂) (A₁ + A₂) := by
  refine ⟨fun f => ?_, fun φ => ?_, fun φq => ?_⟩
  · rw [LinearMap.add_apply, map_add, h₁.1, h₂.1, LinearMap.add_apply]
  · rw [LinearMap.add_apply, LinearMap.add_apply, map_add, h₁.2.1, h₂.2.1]
  · obtain ⟨ψ₁, hψ₁⟩ := h₁.2.2 φq
    obtain ⟨ψ₂, hψ₂⟩ := h₂.2.2 φq
    exact ⟨ψ₁ + ψ₂, by rw [LinearMap.add_apply, hψ₁, hψ₂, ratToComplex_add]⟩

theorem isTwin_mul {P : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ)}
    {t₁ t₂ : Module.End ℂ (CuspForm (Gamma0 N) 2)}
    {A₁ A₂ : (Additive (Gamma0 N) →+ ℂ) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ)}
    (h₁ : IsTwin N P t₁ A₁) (h₂ : IsTwin N P t₂ A₂) : IsTwin N P (t₁ * t₂) (A₁ * A₂) := by
  refine ⟨fun f => ?_, fun φ => ?_, fun φq => ?_⟩
  · rw [Module.End.mul_apply, Module.End.mul_apply, h₁.1, h₂.1]
  · rw [Module.End.mul_apply, Module.End.mul_apply, h₂.2.1, h₁.2.1]
  · obtain ⟨ψ₂, hψ₂⟩ := h₂.2.2 φq
    obtain ⟨ψ₁, hψ₁⟩ := h₁.2.2 ψ₂
    exact ⟨ψ₁, by rw [Module.End.mul_apply, hψ₂, hψ₁]⟩

theorem isTwin_algebraMap (P : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ)) (r : ℤ) :
    IsTwin N P (algebraMap ℤ _ r) (algebraMap ℤ _ r) := by
  refine ⟨fun f => ?_, fun φ => ?_, fun φq => ⟨r • φq, ?_⟩⟩
  · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_zsmul]
  · rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, LinearMap.smul_apply,
      Module.End.one_apply, Module.End.one_apply, map_zsmul]
  · rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      ratToComplex_zsmul]

theorem isTwin_heckeL [NeZero N] (P : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ))
    (ℓ : ℕ) [NeZero ℓ] (t : Module.End ℂ (CuspForm (Gamma0 N) 2))
    (ht : ∀ f, P (t f) = HeckeEis.heckeOperatorHom N ℓ ℂ (P f)) :
    IsTwin N P t (heckeL N ℓ) := by
  refine ⟨ht, fun φ => ?_, fun φq => ⟨HeckeEis.heckeOperatorHom N ℓ ℚ φq, ?_⟩⟩
  · exact (charInvolution_heckeOperatorHom N ℓ ℂ φ).symm
  · rw [heckeL_apply, ratToComplex, ratToComplex, heckeOperatorHom_comp]

theorem exists_twin [NeZero N] (P : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ))
    (hP : ∀ f, P f = periodMap N f) (t : Module.End ℂ (CuspForm (Gamma0 N) 2))
    (ht : t ∈ CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)) :
    ∃ A, IsTwin N P t A := by
  unfold CuspForm.heckeAlgebra at ht
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩
    · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      refine ⟨heckeL N ℓ, isTwin_heckeL P ℓ _ fun f => ?_⟩
      rw [hP, hP]
      exact periodMap_heckeTLin hℓ hℓN f
    · haveI : NeZero q := ⟨hq.ne_zero⟩
      refine ⟨heckeL N q, isTwin_heckeL P q _ fun f => ?_⟩
      rw [hP, hP]
      exact periodMap_heckeULin hq hqN f
  | algebraMap r => exact ⟨_, isTwin_algebraMap P r⟩
  | add x y _ _ hx hy =>
    obtain ⟨A₁, h₁⟩ := hx
    obtain ⟨A₂, h₂⟩ := hy
    exact ⟨_, isTwin_add h₁ h₂⟩
  | mul x y _ _ hx hy =>
    obtain ⟨A₁, h₁⟩ := hx
    obtain ⟨A₂, h₂⟩ := hy
    exact ⟨_, isTwin_mul h₁ h₂⟩

end Twin

section RationalStructure

variable (N : ℕ) [NeZero N]

theorem mem_span_ratToComplex_parabolicHoms (φ : Additive (Gamma0 N) →+ ℂ)
    (hφ : φ ∈ parabolicHoms ℂ (Gamma0 N) ℂ) :
    φ ∈ Submodule.span ℂ (ratToComplex N '' (parabolicHoms ℚ (Gamma0 N) ℚ : Set (Additive (Gamma0 N) →+ ℚ))) := by
  classical
  let bC := Basis.ofVectorSpace ℚ ℂ

  obtain ⟨Sg, hSg, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG (Gamma0 N))
  let F := hfin.toFinset.biUnion fun s => (bC.repr (φ (Additive.ofMul s))).support
  have hsupp : ∀ g : Gamma0 N, (bC.repr (φ (Additive.ofMul g))).support ⊆ F := by
    intro g
    have hg : g ∈ Subgroup.closure Sg := hSg ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      exact Finset.subset_biUnion_of_mem (fun s => (bC.repr (φ (Additive.ofMul s))).support)
        (hfin.mem_toFinset.mpr hx)
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [ofMul_mul, map_add, map_add]
      exact Finsupp.support_add.trans (Finset.union_subset ihx ihy)
    | inv x _ ih =>
      rw [ofMul_inv, map_neg, map_neg, Finsupp.support_neg]
      exact ih

  let φβ : Basis.ofVectorSpaceIndex ℚ ℂ → (Additive (Gamma0 N) →+ ℚ) :=
    fun β => (bC.coord β).toAddMonoidHom.comp φ
  have hφβ : ∀ β γ, φβ β γ = bC.repr (φ γ) β := fun β γ => rfl
  have hφβ_par : ∀ β, φβ β ∈ parabolicHoms ℚ (Gamma0 N) ℚ := by
    intro β γ hγ
    rw [hφβ, hφ γ hγ, map_zero, Finsupp.zero_apply]

  have hexp : φ = ∑ β ∈ F, (bC β : ℂ) • ratToComplex N (φβ β) := by
    refine AddMonoidHom.ext fun γ => ?_
    obtain ⟨g, rfl⟩ : ∃ g, Additive.ofMul g = γ := ⟨Additive.toMul γ, rfl⟩
    rw [AddMonoidHom.finsetSum_apply]
    simp only [AddMonoidHom.smul_apply, ratToComplex_apply, hφβ, smul_eq_mul]
    conv_lhs => rw [← bC.linearCombination_repr (φ (Additive.ofMul g))]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hsupp g) _ (by simp)]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Rat.smul_def, mul_comm]
  rw [hexp]
  exact Submodule.sum_mem _ fun β _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨φβ β, hφβ_par β, rfl⟩)

end RationalStructure

theorem main (N : ℕ) [NeZero N] {ι : Type} (T : ι → CuspForm.heckeAlgebra N 2 (∅ : Set ℕ))
    (hT : LinearIndependent ℤ T) :
    LinearIndependent ℂ
      (fun i => ((T i : CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)) :
        Module.End ℂ (CuspForm (Gamma0 N) 2))) := by
  classical

  obtain ⟨P, hP⟩ := ModularCurve.existsPeriodMapLinear N
  have hPinj : Function.Injective P := fun f g h =>
    ModularCurve.periodMap_injective (by rw [← hP, ← hP, h])
  have hPpar : ∀ f, P f ∈ parabolicHoms ℂ (Gamma0 N) ℂ := fun f => by
    rw [hP]; exact ModularCurve.periodMap_mem_parabolicHoms ℂ f

  choose A hA using fun i => exists_twin P hP (T i : Module.End ℂ (CuspForm (Gamma0 N) 2)) (T i).2
  have htwinP : ∀ (e : ι → ℂ) (s : Finset ι) (f : CuspForm (Gamma0 N) 2),
      P ((∑ j ∈ s, e j • (T j : Module.End ℂ (CuspForm (Gamma0 N) 2))) f) =
        (∑ j ∈ s, e j • A j) (P f) := by
    intro e s f
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, (hA _).1]
  rw [linearIndependent_iff']
  intro s c hc i hi

  let D : (Additive (Gamma0 N) →+ ℂ) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ) := ∑ j ∈ s, c j • A j
  have hD_P : ∀ f, D (P f) = 0 := by
    intro f
    rw [← htwinP c s f, hc, LinearMap.zero_apply, map_zero]
  have hD_inv : ∀ φ, D (charInvolution N ℂ ℂ φ) = charInvolution N ℂ ℂ (D φ) := by
    intro φ
    simp only [D, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, (hA _).2.1]
  have hD_par : ∀ φ ∈ parabolicHoms ℂ (Gamma0 N) ℂ, D φ = 0 := by
    intro φ hφ
    rw [← ModularCurve.periodHomPair_range_eq_parabolicHoms N] at hφ
    obtain ⟨fg, rfl⟩ := LinearMap.mem_range.mp hφ
    obtain ⟨pml, hpml, hpair⟩ := ModularCurve.periodHomPair_def N (ModularCurve.existsPeriodMapLinear N)
    have hpmlP : ∀ f, pml f = P f := fun f => by rw [hpml, hP]
    rw [hpair, LinearMap.coprod_apply]
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      hpmlP, map_add, map_sub, hD_inv, hD_P, map_zero, add_zero, sub_self]

  let bC := Basis.ofVectorSpace ℚ ℂ
  suffices hcoord : ∀ β, bC.repr (c i) β = 0 by
    have h0 : bC.repr (c i) = 0 := Finsupp.ext hcoord
    simpa using h0
  intro β
  let y : ι → ℚ := fun j => bC.repr (c j) β

  have hy : ∀ φq ∈ parabolicHoms ℚ (Gamma0 N) ℚ, (∑ j ∈ s, (y j : ℂ) • A j) (ratToComplex N φq) = 0 := by
    intro φq hφq
    choose ψ hψ using fun j => (hA j).2.2 φq
    have hpar : ratToComplex N φq ∈ parabolicHoms ℂ (Gamma0 N) ℂ := fun γ hγ => by
      rw [ratToComplex_apply, hφq γ hγ, Rat.cast_zero]
    have h0 := hD_par _ hpar
    simp only [D, LinearMap.sum_apply, LinearMap.smul_apply, hψ] at h0
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hψ]
    refine AddMonoidHom.ext fun γ => ?_

    have h1 := congrArg (fun χ : Additive (Gamma0 N) →+ ℂ => bC.repr (χ γ) β) h0
    simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, ratToComplex_apply,
      smul_eq_mul, map_sum, AddMonoidHom.zero_apply, map_zero, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
    have h2 : ∀ j, bC.repr (c j * ((ψ j γ : ℚ) : ℂ)) β = ψ j γ * y j := by
      intro j
      rw [mul_comm, ← Rat.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
    simp only [h2] at h1
    rw [AddMonoidHom.finsetSum_apply, AddMonoidHom.zero_apply]
    simp only [AddMonoidHom.smul_apply, ratToComplex_apply, smul_eq_mul]
    have h3 : (∑ j ∈ s, (y j : ℂ) * ((ψ j γ : ℚ) : ℂ)) = ((∑ j ∈ s, ψ j γ * y j : ℚ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h3, h1, Rat.cast_zero]

  have hyP : ∀ f, (∑ j ∈ s, (y j : ℂ) • A j) (P f) = 0 := by
    intro f
    have hle : Submodule.span ℂ (ratToComplex N '' (parabolicHoms ℚ (Gamma0 N) ℚ :
        Set (Additive (Gamma0 N) →+ ℚ))) ≤ LinearMap.ker (∑ j ∈ s, (y j : ℂ) • A j) := by
      rw [Submodule.span_le]
      rintro _ ⟨φq, hφq, rfl⟩
      exact hy φq hφq
    exact hle (mem_span_ratToComplex_parabolicHoms N (P f) (hPpar f))

  have hyT : (∑ j ∈ s, (y j : ℂ) • (T j : Module.End ℂ (CuspForm (Gamma0 N) 2))) = 0 := by
    refine LinearMap.ext fun f => hPinj ?_
    rw [htwinP, hyP, LinearMap.zero_apply, map_zero]

  let d : ℕ := ∏ j ∈ s, (y j).den
  have hd : (d : ℚ) ≠ 0 := by
    have : 0 < d := Finset.prod_pos fun j _ => (y j).den_pos
    exact_mod_cast this.ne'
  have hm : ∀ j ∈ s, ∃ m : ℤ, (m : ℚ) = y j * d := by
    intro j hj
    obtain ⟨r, hr⟩ : (y j).den ∣ d := Finset.dvd_prod_of_mem (fun j => (y j).den) hj
    refine ⟨(y j).num * r, ?_⟩
    rw [hr]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  choose! m hm using hm
  have hmT : ∑ j ∈ s, m j • T j = 0 := by
    apply Subtype.ext
    have hval : ((∑ j ∈ s, m j • T j : CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)) :
        Module.End ℂ (CuspForm (Gamma0 N) 2)) =
        ∑ j ∈ s, (m j : ℂ) • (T j : Module.End ℂ (CuspForm (Gamma0 N) 2)) := by
      rw [← Subalgebra.val_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, Subalgebra.val_apply, Int.cast_smul_eq_zsmul]
    rw [hval, ZeroMemClass.coe_zero]
    have h2 : (∑ j ∈ s, (m j : ℂ) • (T j : Module.End ℂ (CuspForm (Gamma0 N) 2))) =
        (d : ℂ) • ∑ j ∈ s, (y j : ℂ) • (T j : Module.End ℂ (CuspForm (Gamma0 N) 2)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [smul_smul]
      congr 1
      have h3 : ((m j : ℚ) : ℂ) = ((y j * d : ℚ) : ℂ) := by rw [hm j hj]
      push_cast at h3
      rw [h3, mul_comm]
    rw [h2, hyT, smul_zero]
  have hm0 : m i = 0 := (linearIndependent_iff'.mp hT) s m hmT i hi
  have h4 : y i * d = 0 := by rw [← hm i hi, hm0, Int.cast_zero]
  exact (mul_eq_zero.mp h4).resolve_right hd

end P2mWs11R
p2m_reactivate "P2MW.S_CuspForm_linearIndependent_complex_of_linearIndependent_int.P2mWs11R"

theorem solution (N : ℕ) [NeZero N] {ι : Type}
    (T : ι → CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)) (hT : LinearIndependent ℤ T) :
    LinearIndependent ℂ
      (fun i => ((T i : CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) :=
  P2mWs11R.main N T hT

end S_CuspForm_linearIndependent_complex_of_linearIndependent_int
end P2MW
export P2MW.S_CuspForm_linearIndependent_complex_of_linearIndependent_int (solution)

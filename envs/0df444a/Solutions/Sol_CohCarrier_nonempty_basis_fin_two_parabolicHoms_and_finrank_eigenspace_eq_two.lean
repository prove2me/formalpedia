-- Prove2me | solution 1 for CohCarrier.nonempty_basis_fin_two_parabolicHoms_and_finrank_eigenspace_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2be5cd35-29fa-5cef-9a64-f538e4fb1601

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_PeriodHomPair
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CohCarrier_exists_heckeAlgebra_ringHom_parabolicHoms_H1_top
import Theorems.Thm_CuspForm_exists_top_eq_heckeAlgebra_adjoin_smul
import Theorems.Thm_CuspForm_heckeAlgebra_adjoin_exists_frobenius_form
import Theorems.Thm_CuspForm_heckeTLin_mem_adjoin_heckeTLin_of_finite
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_and_finrank_eigenspace_eq_two
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

noncomputable section

open ModularCurve.Period
open scoped IsMulCommutative

namespace ESD3C2

variable (N : ℕ) [NeZero N]

abbrev S2 : Type := CuspForm (CongruenceSubgroup.Gamma0 N) 2

abbrev V : Type := ↥(parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ)

scoped instance instAddCommGroupV : AddCommGroup (V N) := Submodule.addCommGroup _

scoped instance (priority := 10000) instAddCommMonoidV : AddCommMonoid (V N) :=
  (instAddCommGroupV N).toAddCommMonoid

scoped instance : FiniteDimensional ℂ (S2 N) := CuspForm.finiteDimensional_Gamma0 N 2

abbrev 𝔸 : Subalgebra ℂ (Module.End ℂ (S2 N)) :=
  Algebra.adjoin ℂ ((CuspForm.heckeAlgebra N 2 ∅ : Set (Module.End ℂ (S2 N))))

scoped instance : FiniteDimensional ℂ ↥(𝔸 N) :=
  inferInstanceAs (FiniteDimensional ℂ ↥(Subalgebra.toSubmodule (𝔸 N)))

theorem commute_𝔸 (x y : ↥(𝔸 N)) : x * y = y * x := mul_comm x y

section Psi

variable {N}
variable (E : (S2 N × S2 N) ≃ₗ[ℂ] V N)

def Ψ : Module.End ℂ (S2 N) →ₐ[ℂ] Module.End ℂ (V N) where
  toFun t := E.toLinearMap ∘ₗ (t.prodMap t) ∘ₗ E.symm.toLinearMap
  map_one' := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap 1 1 (E.symm v)) = v
    rw [LinearMap.prodMap_one]
    exact E.apply_symm_apply v
  map_mul' s t := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (s * t) (s * t) (E.symm v)) =
      E (LinearMap.prodMap s s (E.symm (E (LinearMap.prodMap t t (E.symm v)))))
    rw [E.symm_apply_apply]
    rfl
  map_zero' := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap 0 0 (E.symm v)) = 0
    rw [LinearMap.prodMap_zero, LinearMap.zero_apply, map_zero]
  map_add' s t := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (s + t) (s + t) (E.symm v)) =
      E (LinearMap.prodMap s s (E.symm v)) + E (LinearMap.prodMap t t (E.symm v))
    rw [← map_add]
    rfl
  commutes' c := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (algebraMap ℂ (Module.End ℂ (S2 N)) c)
      (algebraMap ℂ (Module.End ℂ (S2 N)) c) (E.symm v)) = (algebraMap ℂ (Module.End ℂ (V N)) c) v
    rw [Module.algebraMap_end_eq_smul_id, Module.algebraMap_end_eq_smul_id]
    change E (c • (E.symm v).1, c • (E.symm v).2) = c • v
    rw [← Prod.smul_mk, map_smul]
    exact congrArg (c • ·) (E.apply_symm_apply v)

theorem Ψ_apply_E (t : Module.End ℂ (S2 N)) (f g : S2 N) : Ψ E t (E (f, g)) = E (t f, t g) := by
  change E (LinearMap.prodMap t t (E.symm (E (f, g)))) = _
  rw [E.symm_apply_apply]
  rfl

theorem Ψ_injective : Function.Injective (Ψ E) := by
  intro s t h
  apply LinearMap.ext
  intro f
  have := congrArg (fun x : Module.End ℂ (V N) => (E.symm (x (E (f, 0)))).1) h
  simp only [Ψ_apply_E, LinearEquiv.symm_apply_apply] at this
  exact this

end Psi

section Main

variable (S : Set ℕ) (hSfin : S.Finite) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S)

def G : Set (Module.End ℂ (V N)) :=
  {T : Module.End ℂ (V N) | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
    ((T v : V N) : CohCarrier.H1 N ⊤ ℂ) = CohCarrier.heckeT N ⊤ ℓ ℂ (v : CohCarrier.H1 N ⊤ ℂ)}

def A : Subalgebra ℂ (Module.End ℂ (V N)) := Algebra.adjoin ℂ (G N S)

theorem A_def : A N S = Algebra.adjoin ℂ (G N S) := rfl

variable {N S}
variable (ρ : CuspForm.heckeAlgebra N 2 ∅ →+* Module.End ℂ (V N))
  (E : (S2 N × S2 N) ≃ₗ[ℂ] V N)
  (hE : ∀ (t : CuspForm.heckeAlgebra N 2 ∅) (f g : S2 N),
    E ((t : Module.End ℂ (S2 N)) f, (t : Module.End ℂ (S2 N)) g) = ρ t (E (f, g)))
  (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (∅ : Set ℕ)) (φ : V N),
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((ρ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) φ : V N) : CohCarrier.H1 N ⊤ ℂ) =
      CohCarrier.heckeT N ⊤ ℓ ℂ (φ : CohCarrier.H1 N ⊤ ℂ))
  (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ (∅ : Set ℕ)) (φ : V N),
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ((ρ (CuspForm.heckeAlgebra.U hq hqN hqS) φ : V N) : CohCarrier.H1 N ⊤ ℂ) =
      CohCarrier.heckeT N ⊤ q ℂ (φ : CohCarrier.H1 N ⊤ ℂ))

include hE in
theorem Ψ_coe (t : CuspForm.heckeAlgebra N 2 ∅) : Ψ E (t : Module.End ℂ (S2 N)) = ρ t := by
  apply LinearMap.ext
  intro v
  obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
  rw [Ψ_apply_E, hE]

def genOp (ℓ : ℕ) (hℓ : ℓ.Prime) : Module.End ℂ (S2 N) := by
  classical
  exact if h : ℓ ∣ N then CuspForm.heckeULin 2 h else CuspForm.heckeTLin 2 hℓ h

theorem genOp_mem (ℓ : ℕ) (hℓ : ℓ.Prime) : genOp (N := N) ℓ hℓ ∈ CuspForm.heckeAlgebra N 2 ∅ := by
  unfold genOp
  split_ifs with h
  · exact CuspForm.heckeULin_mem_heckeAlgebra hℓ h (Set.notMem_empty ℓ)
  · exact CuspForm.heckeTLin_mem_heckeAlgebra hℓ h (Set.notMem_empty ℓ)

include hE hT hU in

theorem coe_Ψ_genOp (ℓ : ℕ) (hℓ : ℓ.Prime) (v : V N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((Ψ E (genOp (N := N) ℓ hℓ) v : V N) : CohCarrier.H1 N ⊤ ℂ) =
      CohCarrier.heckeT N ⊤ ℓ ℂ (v : CohCarrier.H1 N ⊤ ℂ) := by
  unfold genOp
  split_ifs with h
  · have := Ψ_coe ρ E hE (CuspForm.heckeAlgebra.U hℓ h (Set.notMem_empty ℓ))
    rw [CuspForm.heckeAlgebra.coe_U] at this
    rw [this]
    exact hU ℓ hℓ h (Set.notMem_empty ℓ) v
  · have := Ψ_coe ρ E hE (CuspForm.heckeAlgebra.T hℓ h (Set.notMem_empty ℓ))
    rw [CuspForm.heckeAlgebra.coe_T] at this
    rw [this]
    exact hT ℓ hℓ h (Set.notMem_empty ℓ) v

include hE hT hU in

theorem G_eq : G N S = {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ T = Ψ E (genOp (N := N) ℓ hℓ)} := by
  ext T
  constructor
  · rintro ⟨ℓ, hℓ, hℓS, h⟩
    refine ⟨ℓ, hℓ, hℓS, ?_⟩
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [h v, coe_Ψ_genOp ρ E hE hT hU]
  · rintro ⟨ℓ, hℓ, hℓS, rfl⟩
    exact ⟨ℓ, hℓ, hℓS, fun v => coe_Ψ_genOp ρ E hE hT hU ℓ hℓ v⟩

theorem 𝔸_eq_adjoin_genOp :
    𝔸 N = Algebra.adjoin ℂ {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), T = genOp (N := N) ℓ hℓ} := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    intro x hx
    change x ∈ Algebra.adjoin ℤ (CuspForm.heckeGenerators N 2 ∅) at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      refine Algebra.subset_adjoin ?_
      rcases hx with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩
      · exact ⟨ℓ, hℓ, by unfold genOp; rw [dif_neg hℓN]⟩
      · exact ⟨q, hq, by unfold genOp; rw [dif_pos hqN]⟩
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Subalgebra.zsmul_mem _ (Subalgebra.one_mem _) r
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨ℓ, hℓ, rfl⟩
    exact Algebra.subset_adjoin (genOp_mem ℓ hℓ)

include hSfin hS hE hT hU in

theorem A_eq_map : A N S = (𝔸 N).map (Ψ E) := by
  rw [𝔸_eq_adjoin_genOp, AlgHom.map_adjoin, A_def, G_eq ρ E hE hT hU]
  apply le_antisymm
  · refine Algebra.adjoin_mono ?_
    rintro _ ⟨ℓ, hℓ, -, rfl⟩
    exact ⟨genOp ℓ hℓ, ⟨ℓ, hℓ, rfl⟩, rfl⟩
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨_, ⟨ℓ, hℓ, rfl⟩, rfl⟩
    by_cases hℓS : ℓ ∈ S
    ·
      have hℓN : ¬ ℓ ∣ N := fun h => hS ℓ hℓ h hℓS
      have hgen : genOp (N := N) ℓ hℓ = CuspForm.heckeTLin 2 hℓ hℓN := by
        unfold genOp; rw [dif_neg hℓN]
      have hmem := CuspForm.heckeTLin_mem_adjoin_heckeTLin_of_finite N S hSfin hℓ hℓN
      have hmap : Ψ E (CuspForm.heckeTLin 2 hℓ hℓN) ∈ (Algebra.adjoin ℂ
          {T : Module.End ℂ (S2 N) | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
            ℓ ∉ S ∧ T = CuspForm.heckeTLin 2 hℓ hℓN}).map (Ψ E) :=
        Subalgebra.mem_map.mpr ⟨_, hmem, rfl⟩
      rw [AlgHom.map_adjoin] at hmap
      rw [hgen]
      refine (Algebra.adjoin_mono ?_) hmap
      rintro _ ⟨_, ⟨ℓ', hℓ', hℓ'N, hℓ'S, rfl⟩, rfl⟩
      refine ⟨ℓ', hℓ', hℓ'S, ?_⟩
      unfold genOp; rw [dif_neg hℓ'N]
    · exact Algebra.subset_adjoin ⟨ℓ, hℓ, hℓS, rfl⟩

variable (f₀ : S2 N) (hf₀ : ∀ g : S2 N, ∃ T : ↥(𝔸 N), (T : Module.End ℂ (S2 N)) f₀ = g)

include hf₀ in
theorem eq_zero_of_apply_f₀ (t : ↥(𝔸 N)) (ht : (t : Module.End ℂ (S2 N)) f₀ = 0) : t = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro g
  obtain ⟨T, hT⟩ := hf₀ g
  have hc : (t : Module.End ℂ (S2 N)) * T = T * t := congrArg Subtype.val (commute_𝔸 N t T)
  calc (t : Module.End ℂ (S2 N)) g = ((t : Module.End ℂ (S2 N)) * T) f₀ := by
          rw [Module.End.mul_apply, hT]
    _ = ((T : Module.End ℂ (S2 N)) * t) f₀ := by rw [hc]
    _ = 0 := by rw [Module.End.mul_apply, ht, map_zero]
    _ = (0 : Module.End ℂ (S2 N)) g := rfl

def κ : (↥(𝔸 N) × ↥(𝔸 N)) →ₗ[ℂ] V N :=
  E.toLinearMap ∘ₗ
    (((LinearMap.applyₗ f₀).comp (𝔸 N).val.toLinearMap).prodMap
      ((LinearMap.applyₗ f₀).comp (𝔸 N).val.toLinearMap))

theorem κ_apply (t : ↥(𝔸 N) × ↥(𝔸 N)) :
    κ E f₀ t = E ((t.1 : Module.End ℂ (S2 N)) f₀, (t.2 : Module.End ℂ (S2 N)) f₀) := rfl

include hf₀ in
theorem κ_bijective : Function.Bijective (κ E f₀) := by
  constructor
  · intro s t h
    rw [κ_apply, κ_apply] at h
    have h' := E.injective h
    simp only [Prod.mk.injEq] at h'
    have h1 : s.1 - t.1 = 0 := eq_zero_of_apply_f₀ f₀ hf₀ _ (by
      rw [Subalgebra.coe_sub, LinearMap.sub_apply, h'.1, sub_self])
    have h2 : s.2 - t.2 = 0 := eq_zero_of_apply_f₀ f₀ hf₀ _ (by
      rw [Subalgebra.coe_sub, LinearMap.sub_apply, h'.2, sub_self])
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  · intro v
    obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
    obtain ⟨T₀, hT₀⟩ := hf₀ f
    obtain ⟨T₁, hT₁⟩ := hf₀ g
    exact ⟨(T₀, T₁), by rw [κ_apply, hT₀, hT₁]⟩

variable (hA : A N S = (𝔸 N).map (Ψ E))

def bv : Fin 2 → V N := ![E (f₀, 0), E (0, f₀)]

include hA in
theorem exists_of_mem_A (a : ↥(A N S)) : ∃ t : ↥(𝔸 N), (a : Module.End ℂ (V N)) = Ψ E t := by
  have ha : (a : Module.End ℂ (V N)) ∈ (𝔸 N).map (Ψ E) := hA ▸ a.2
  obtain ⟨t, ht, hta⟩ := Subalgebra.mem_map.mp ha
  exact ⟨⟨t, ht⟩, hta.symm⟩

theorem smul_bv_sum (t₀ t₁ : ↥(𝔸 N)) :
    (Ψ E t₀) (E (f₀, 0)) + (Ψ E t₁) (E (0, f₀)) =
      E ((t₀ : Module.End ℂ (S2 N)) f₀, (t₁ : Module.End ℂ (S2 N)) f₀) := by
  rw [Ψ_apply_E, Ψ_apply_E, map_zero, map_zero, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

include hf₀ hA in
theorem linearIndependent_bv : LinearIndependent ↥(A N S) (bv E f₀) := by
  refine (Fintype.linearIndependent_iff (ι := Fin 2) (R := ↥(A N S)) (v := bv E f₀)).mpr ?_
  intro c hc
  obtain ⟨t₀, ht₀⟩ := exists_of_mem_A E hA (c 0)
  obtain ⟨t₁, ht₁⟩ := exists_of_mem_A E hA (c 1)
  rw [Fin.sum_univ_two] at hc
  change (c 0 : Module.End ℂ (V N)) (E (f₀, 0)) + (c 1 : Module.End ℂ (V N)) (E (0, f₀)) = 0 at hc
  rw [ht₀, ht₁, smul_bv_sum, ← κ_apply E f₀ (t₀, t₁)] at hc
  have h0 : (t₀, t₁) = 0 := (κ_bijective E f₀ hf₀).1 (hc.trans (map_zero _).symm)
  simp only [Prod.mk_eq_zero] at h0
  intro i
  fin_cases i
  · apply Subtype.ext; change (c 0 : Module.End ℂ (V N)) = 0; rw [ht₀, h0.1]; exact map_zero _
  · apply Subtype.ext; change (c 1 : Module.End ℂ (V N)) = 0; rw [ht₁, h0.2]; exact map_zero _

include hf₀ hA in
theorem span_bv : ⊤ ≤ Submodule.span ↥(A N S) (Set.range (bv E f₀)) := by
  intro v _
  obtain ⟨⟨t₀, t₁⟩, rfl⟩ := (κ_bijective E f₀ hf₀).2 v
  rw [κ_apply, ← smul_bv_sum]
  have hm0 : Ψ E t₀ ∈ A N S := by rw [hA]; exact Subalgebra.mem_map.mpr ⟨_, t₀.2, rfl⟩
  have hm1 : Ψ E t₁ ∈ A N S := by rw [hA]; exact Subalgebra.mem_map.mpr ⟨_, t₁.2, rfl⟩
  have e0 : (Ψ E t₀) (E (f₀, 0)) = (⟨Ψ E t₀, hm0⟩ : ↥(A N S)) • bv E f₀ 0 := rfl
  have e1 : (Ψ E t₁) (E (0, f₀)) = (⟨Ψ E t₁, hm1⟩ : ↥(A N S)) • bv E f₀ 1 := rfl
  rw [e0, e1]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

def basisA : Module.Basis (Fin 2) ↥(A N S) (V N) :=
  Module.Basis.mk (linearIndependent_bv E f₀ hf₀ hA) (span_bv E f₀ hf₀ hA)

def eig𝔸 (χ' : ↥(𝔸 N) → ℂ) : Submodule ℂ ↥(𝔸 N) where
  carrier := {x | ∀ t : ↥(𝔸 N), t * x = χ' t • x}
  zero_mem' t := by simp
  add_mem' {x y} hx hy t := by rw [mul_add, hx t, hy t, smul_add]
  smul_mem' c x hx t := by rw [mul_smul_comm, hx t, smul_comm]

theorem mem_eig𝔸 {χ' : ↥(𝔸 N) → ℂ} {x : ↥(𝔸 N)} : x ∈ eig𝔸 (N := N) χ' ↔ ∀ t : ↥(𝔸 N), t * x = χ' t • x :=
  Iff.rfl

section Line

variable (l : ↥(𝔸 N) →ₗ[ℂ] ℂ) (hl : ∀ a : ↥(𝔸 N), (∀ b, l (a * b) = 0) → a = 0)

def θ : ↥(𝔸 N) →ₗ[ℂ] Module.Dual ℂ ↥(𝔸 N) :=
  (LinearMap.mul ℂ ↥(𝔸 N)).compr₂ l

theorem θ_apply (x y : ↥(𝔸 N)) : θ l x y = l (x * y) := rfl

include hl in
theorem θ_injective : Function.Injective (θ l) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  apply hl x
  intro b
  have := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) b
  exact this

include hl in
theorem θ_bijective : Function.Bijective (θ l) := by
  refine ⟨θ_injective l hl, ?_⟩
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj (θ_injective l hl), Subspace.dual_finrank_eq]

include hl in

theorem eig𝔸_line (χ' : ↥(𝔸 N) →ₐ[ℂ] ℂ) :
    ∃ x₀ : ↥(𝔸 N), x₀ ∈ eig𝔸 (N := N) χ' ∧ x₀ ≠ 0 ∧
      ∀ y ∈ eig𝔸 (N := N) χ', ∃ c : ℂ, y = c • x₀ := by

  obtain ⟨x₀, hx₀⟩ := (θ_bijective l hl).2 χ'.toLinearMap
  have hx₀mem : x₀ ∈ eig𝔸 (N := N) χ' := by
    intro t
    apply θ_injective l hl
    apply LinearMap.ext
    intro y
    have h1 : θ l (t * x₀) y = χ' (t * y) := by
      rw [θ_apply, mul_comm t x₀, mul_assoc, ← θ_apply, hx₀]; rfl
    have h2 : θ l (χ' t • x₀) y = χ' t * χ' y := by
      rw [map_smul, LinearMap.smul_apply, hx₀, smul_eq_mul]; rfl
    rw [h1, h2, map_mul]
  have hval : l (x₀ * 1) = 1 := by
    rw [← θ_apply, hx₀]
    exact map_one χ'
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h, zero_mul, map_zero] at hval
    exact zero_ne_one hval
  have hlx : l x₀ = 1 := by rw [← mul_one x₀]; exact hval
  refine ⟨x₀, hx₀mem, hx₀ne, fun y hy => ⟨l y, ?_⟩⟩

  have key : ∀ z ∈ eig𝔸 (N := N) χ', l z = 0 → z = 0 := by
    intro z hz h0
    apply θ_injective l hl
    apply LinearMap.ext
    intro y
    rw [θ_apply, LinearMap.map_zero, LinearMap.zero_apply, mul_comm z y, hz y, map_smul, h0,
      smul_zero]
  have hmem : y - l y • x₀ ∈ eig𝔸 (N := N) χ' :=
    Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hx₀mem)
  have h0 : l (y - l y • x₀) = 0 := by
    rw [map_sub, map_smul, hlx, smul_eq_mul, mul_one, sub_self]
  exact sub_eq_zero.mp (key _ hmem h0)

end Line

include hf₀ hA in

theorem finrank_eigenspace_eq_two (χ : ↥(A N S) →ₐ[ℂ] ℂ) (χ' : ↥(𝔸 N) → ℂ)
    (hχ' : ∀ t : ↥(𝔸 N), χ' t = χ ⟨Ψ E t, hA ▸ Subalgebra.mem_map.mpr ⟨_, t.2, rfl⟩⟩)
    (x₀ : ↥(𝔸 N)) (hx₀ : x₀ ∈ eig𝔸 (N := N) χ') (hx₀ne : x₀ ≠ 0)
    (hline : ∀ y ∈ eig𝔸 (N := N) χ', ∃ c : ℂ, y = c • x₀) :
    Module.finrank ℂ ↥(⨅ a : ↥(A N S), Module.End.eigenspace (a : Module.End ℂ (V N)) (χ a)) = 2 := by
  set Eχ := ⨅ a : ↥(A N S), Module.End.eigenspace (a : Module.End ℂ (V N)) (χ a) with hEχ

  have hmem : ∀ t : ↥(𝔸 N) × ↥(𝔸 N), κ E f₀ t ∈ Eχ ↔ t.1 ∈ eig𝔸 (N := N) χ' ∧ t.2 ∈ eig𝔸 (N := N) χ' := by
    intro t
    rw [hEχ, Submodule.mem_iInf]
    constructor
    · intro h
      have key : ∀ s : ↥(𝔸 N), s * t.1 = χ' s • t.1 ∧ s * t.2 = χ' s • t.2 := by
        intro s
        have hs := h ⟨Ψ E s, hA ▸ Subalgebra.mem_map.mpr ⟨_, s.2, rfl⟩⟩
        rw [Module.End.mem_eigenspace_iff] at hs
        change Ψ E s (κ E f₀ t) = _ at hs
        rw [← hχ', κ_apply, Ψ_apply_E, ← map_smul, Prod.smul_mk] at hs
        have hs' := E.injective hs
        rw [Prod.mk.injEq] at hs'
        obtain ⟨hs1, hs2⟩ := hs'
        constructor
        · have := eq_zero_of_apply_f₀ f₀ hf₀ (s * t.1 - χ' s • t.1) (by
            rw [Subalgebra.coe_sub, LinearMap.sub_apply, Subalgebra.coe_smul, LinearMap.smul_apply,
              Subalgebra.coe_mul, Module.End.mul_apply, hs1, sub_self])
          exact sub_eq_zero.mp this
        · have := eq_zero_of_apply_f₀ f₀ hf₀ (s * t.2 - χ' s • t.2) (by
            rw [Subalgebra.coe_sub, LinearMap.sub_apply, Subalgebra.coe_smul, LinearMap.smul_apply,
              Subalgebra.coe_mul, Module.End.mul_apply, hs2, sub_self])
          exact sub_eq_zero.mp this
      exact ⟨fun s => (key s).1, fun s => (key s).2⟩
    · rintro ⟨h1, h2⟩ a
      obtain ⟨s, hs⟩ := exists_of_mem_A E hA a
      rw [Module.End.mem_eigenspace_iff]
      change (a : Module.End ℂ (V N)) (κ E f₀ t) = _
      have ha : a = ⟨Ψ E s, hA ▸ Subalgebra.mem_map.mpr ⟨_, s.2, rfl⟩⟩ := Subtype.ext hs
      rw [hs, κ_apply, Ψ_apply_E, ha, ← hχ', ← map_smul, Prod.smul_mk]
      have e1 : (s : Module.End ℂ (S2 N)) ((t.1 : Module.End ℂ (S2 N)) f₀) = χ' s • ((t.1 : Module.End ℂ (S2 N)) f₀) := by
        have := congrArg (fun x : ↥(𝔸 N) => (x : Module.End ℂ (S2 N)) f₀) (h1 s)
        simpa using this
      have e2 : (s : Module.End ℂ (S2 N)) ((t.2 : Module.End ℂ (S2 N)) f₀) = χ' s • ((t.2 : Module.End ℂ (S2 N)) f₀) := by
        have := congrArg (fun x : ↥(𝔸 N) => (x : Module.End ℂ (S2 N)) f₀) (h2 s)
        simpa using this
      rw [e1, e2]

  have hxf : (x₀ : Module.End ℂ (S2 N)) f₀ ≠ 0 := fun h => hx₀ne (eq_zero_of_apply_f₀ f₀ hf₀ x₀ h)

  let φ : (ℂ × ℂ) →ₗ[ℂ] ↥Eχ :=
    { toFun := fun c => ⟨κ E f₀ (c.1 • x₀, c.2 • x₀),
        (hmem _).mpr ⟨Submodule.smul_mem _ _ hx₀, Submodule.smul_mem _ _ hx₀⟩⟩
      map_add' := fun c d => by
        apply Subtype.ext
        change κ E f₀ ((c.1 + d.1) • x₀, (c.2 + d.2) • x₀) =
          κ E f₀ (c.1 • x₀, c.2 • x₀) + κ E f₀ (d.1 • x₀, d.2 • x₀)
        rw [← map_add, Prod.mk_add_mk, add_smul, add_smul]
      map_smul' := fun r c => by
        apply Subtype.ext
        change κ E f₀ ((r * c.1) • x₀, (r * c.2) • x₀) = r • κ E f₀ (c.1 • x₀, c.2 • x₀)
        rw [← map_smul, Prod.smul_mk, smul_smul, smul_smul] }
  have hφ : Function.Bijective φ := by
    constructor
    · intro c d h
      have h' := congrArg (fun z : ↥Eχ => (z : V N)) h
      change κ E f₀ _ = κ E f₀ _ at h'
      rw [κ_apply, κ_apply] at h'
      have h'' := E.injective h'
      simp only [Prod.mk.injEq, Subalgebra.coe_smul, LinearMap.smul_apply] at h''
      obtain ⟨ha, hb⟩ := h''
      have ha' : (c.1 - d.1) • (x₀ : Module.End ℂ (S2 N)) f₀ = 0 := by rw [sub_smul, ha, sub_self]
      have hb' : (c.2 - d.2) • (x₀ : Module.End ℂ (S2 N)) f₀ = 0 := by rw [sub_smul, hb, sub_self]
      rw [smul_eq_zero] at ha' hb'
      exact Prod.ext (sub_eq_zero.mp (ha'.resolve_right hxf)) (sub_eq_zero.mp (hb'.resolve_right hxf))
    · rintro ⟨v, hv⟩
      obtain ⟨t, rfl⟩ := (κ_bijective E f₀ hf₀).2 v
      obtain ⟨h1, h2⟩ := (hmem t).mp hv
      obtain ⟨a, ha⟩ := hline t.1 h1
      obtain ⟨b, hb⟩ := hline t.2 h2
      refine ⟨(a, b), Subtype.ext ?_⟩
      change κ E f₀ (a • x₀, b • x₀) = κ E f₀ t
      rw [← ha, ← hb]
  rw [← (LinearEquiv.ofBijective φ hφ).finrank_eq, Module.finrank_prod, Module.finrank_self]

end Main

theorem main (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S) :
    Nonempty (Module.Basis (Fin 2) ↥(A N S) (V N)) ∧
    ∀ χ : ↥(A N S) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(A N S), Module.End.eigenspace (a : Module.End ℂ (V N)) (χ a)) = 2 := by
  obtain ⟨ρ, E, -, hE, hT, hU, -⟩ := CohCarrier.exists_heckeAlgebra_ringHom_parabolicHoms_H1_top N ∅
  obtain ⟨f₀, hf₀⟩ := CuspForm.exists_top_eq_heckeAlgebra_adjoin_smul N
  obtain ⟨l, hl⟩ := CuspForm.heckeAlgebra_adjoin_exists_frobenius_form N
  have hA : A N S = (𝔸 N).map (Ψ E) := A_eq_map hSfin hS ρ E hE hT hU
  refine ⟨Nonempty.intro (basisA (S := S) E f₀ hf₀ hA), fun χ => ?_⟩

  let e1 : ↥(𝔸 N) ≃ₐ[ℂ] ↥((𝔸 N).map (Ψ E)) := Subalgebra.equivMapOfInjective _ _ (Ψ_injective E)
  let e2 : ↥((𝔸 N).map (Ψ E)) ≃ₐ[ℂ] ↥(A N S) := Subalgebra.equivOfEq _ _ hA.symm
  let χ' : ↥(𝔸 N) →ₐ[ℂ] ℂ := (χ.comp e2.toAlgHom).comp e1.toAlgHom
  have hχ' : ∀ t : ↥(𝔸 N), χ' t = χ ⟨Ψ E t, hA ▸ Subalgebra.mem_map.mpr ⟨_, t.2, rfl⟩⟩ := by
    intro t
    change χ (e2 (e1 t)) = _
    congr 1
  obtain ⟨x₀, hx₀, hx₀ne, hline⟩ := eig𝔸_line l hl χ'
  exact finrank_eigenspace_eq_two E f₀ hf₀ hA χ χ' hχ' x₀ hx₀ hx₀ne hline

end ESD3C2
p2m_reactivate "P2MW.S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_and_finrank_eigenspace_eq_two.ESD3C2"

theorem solution
    (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S) :
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ) |
            ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ)) :
                CohCarrier.H1 N ⊤ ℂ) = CohCarrier.heckeT N ⊤ ℓ ℂ (v : CohCarrier.H1 N ⊤ ℂ)})
      ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ)) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ) |
            ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ)) :
                CohCarrier.H1 N ⊤ ℂ) = CohCarrier.heckeT N ⊤ ℓ ℂ (v : CohCarrier.H1 N ⊤ ℂ)}) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ) |
            ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ)) :
                CohCarrier.H1 N ⊤ ℂ) = CohCarrier.heckeT N ⊤ ℓ ℂ (v : CohCarrier.H1 N ⊤ ℂ)}),
        Module.End.eigenspace (a : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH N ⊤) ℂ)) (χ a)) = 2 :=
  ESD3C2.main N S hSfin hS

end
end S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_and_finrank_eigenspace_eq_two
end P2MW
export P2MW.S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_and_finrank_eigenspace_eq_two (solution)

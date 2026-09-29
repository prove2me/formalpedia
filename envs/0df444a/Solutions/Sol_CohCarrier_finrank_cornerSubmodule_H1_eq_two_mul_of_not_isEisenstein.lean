-- Prove2me | solution 1 for CohCarrier.finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/13c44fd5-2b7c-57c8-a38c-09885d325c3f

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
import Theorems.Thm_CohCarrier_nonempty_basis_fin_two_parabolicHoms_and_finrank_eigenspace_eq_two
import Theorems.Thm_Matrix_finrank_range_and_eigenspace_of_adjoin_intCast
import Theorems.Thm_CohCarrier_exists_basis_parabolicHoms_top_two_mul_finrank
import Theorems.Thm_CohCarrier_heckeT_top_apply_eq_heckeOperatorHom
import Theorems.Thm_ModularCurve_Period_heckeOperatorHom_preserves_parabolic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

noncomputable section

open Module IharaLemma

namespace ESD3

section CornerRing

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable (Sp : IdempotentSplitting B) (i : Fin Sp.n)

theorem toCornerRing_e : Sp.toCornerRing i (Sp.e i) = 1 := by
  apply Subtype.ext
  show Sp.e i * Sp.e i * Sp.e i = Sp.e i
  rw [(Sp.idem i).eq, (Sp.idem i).eq]

theorem toCornerRing_algebraMap (r : 𝒪) :
    Sp.toCornerRing i (algebraMap 𝒪 B r) = algebraMap 𝒪 (Sp.CornerRing i) r := rfl

theorem 𝔪_eq_ker {k : Type} [Field k] [Algebra 𝒪 k] (hsurj : Function.Surjective (algebraMap 𝒪 k))
    (πk : Sp.CornerRing i →ₐ[𝒪] k) :
    Sp.𝔪 i = RingHom.ker (πk.toRingHom.comp (Sp.toCornerRing i)) := by
  set f : B →+* k := πk.toRingHom.comp (Sp.toCornerRing i) with hf
  have hfsurj : Function.Surjective f := by
    intro x
    obtain ⟨r, rfl⟩ := hsurj x
    refine ⟨algebraMap 𝒪 B r, ?_⟩
    show πk (Sp.toCornerRing i (algebraMap 𝒪 B r)) = _
    rw [toCornerRing_algebraMap, AlgHom.commutes]
  have hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hfsurj
  obtain ⟨j, hj⟩ := Sp.exists_eq _ hmax
  have hnot : Sp.e i ∉ RingHom.ker f := by
    intro h
    rw [RingHom.mem_ker] at h
    change πk (Sp.toCornerRing i (Sp.e i)) = 0 at h
    rw [toCornerRing_e, map_one] at h
    exact one_ne_zero h
  by_cases hji : j = i
  · subst hji; exact hj
  · exact absurd (hj ▸ Sp.mem_of_ne (Ne.symm hji)) hnot

theorem exists_mul_mul_e_eq {u : B} (hu : u ∉ Sp.𝔪 i) : ∃ t : B, t * u * Sp.e i = Sp.e i :=
  exists_mul_mul_eq_of_notMem (Sp.idem i) (Sp.𝔪 i) (Sp.mem_of_isMaximal_of_ne i) hu

end CornerRing

theorem algHom_eq_of_isLocalRing {𝒪 : Type} [CommRing 𝒪] {C : Type} [CommRing C] [IsLocalRing C]
    [Algebra 𝒪 C] {k : Type} [Field k] [Algebra 𝒪 k]
    (hsurj : Function.Surjective (algebraMap 𝒪 k)) (f g : C →ₐ[𝒪] k) : f = g := by
  have hker : ∀ h : C →ₐ[𝒪] k, RingHom.ker h.toRingHom = IsLocalRing.maximalIdeal C := by
    intro h
    have hs : Function.Surjective h.toRingHom := by
      intro x
      obtain ⟨r, rfl⟩ := hsurj x
      exact ⟨algebraMap 𝒪 C r, h.commutes r⟩
    exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hs)
  ext x
  obtain ⟨r, hr⟩ := hsurj (f x)
  have hx : x - algebraMap 𝒪 C r ∈ IsLocalRing.maximalIdeal C := by
    rw [← hker f, RingHom.mem_ker]
    show f (x - algebraMap 𝒪 C r) = 0
    rw [map_sub, AlgHom.commutes, hr, sub_self]
  rw [← hker g, RingHom.mem_ker] at hx
  change g (x - algebraMap 𝒪 C r) = 0 at hx
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at hx
  rw [hx, hr]

section Module

variable (𝒪 : Type) [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
variable (Sp : IdempotentSplitting B) (i : Fin Sp.n)
variable (W : Submodule 𝒪 V) (hW : ∀ (b : B) (v : V), v ∈ W → b • v ∈ W)

def act (b : B) : V →ₗ[𝒪] V where
  toFun v := b • v
  map_add' v w := smul_add b v w
  map_smul' r v := smul_comm b r v

@[scoped simp] theorem act_apply (b : B) (v : V) : act 𝒪 b v = b • v := rfl

def resAlg : B →ₐ[𝒪] Module.End 𝒪 W where
  toFun b := (act 𝒪 b).restrict fun v hv => hW b v hv
  map_one' := by ext w; simp
  map_mul' a b := by ext w; simp [mul_smul]
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp [add_smul]
  commutes' r := by
    ext w
    simp [Algebra.algebraMap_eq_smul_one]

@[scoped simp] theorem coe_resAlg_apply (b : B) (w : W) : ((resAlg 𝒪 W hW b w : W) : V) = b • (w : V) := rfl

include hW in

theorem e_smul_mem {u : B} (hu : u ∉ Sp.𝔪 i) (huW : ∀ v : V, u • v ∈ W) (v : V) :
    Sp.e i • v ∈ W := by
  obtain ⟨t, ht⟩ := exists_mul_mul_e_eq Sp i hu
  rw [← ht, mul_smul, mul_smul]
  exact hW t _ (huW _)

def eigen (lam : B → 𝒪) : Submodule 𝒪 V where
  carrier := {v | ∀ b : B, b • v = lam b • v}
  zero_mem' b := by simp
  add_mem' {v w} hv hw b := by rw [smul_add, hv b, hw b, smul_add]
  smul_mem' r v hv b := by rw [smul_comm, hv b, smul_comm]

theorem mem_eigen {lam : B → 𝒪} {v : V} : v ∈ eigen 𝒪 lam ↔ ∀ b : B, b • v = lam b • v := Iff.rfl

theorem eigen_le {lam : B → 𝒪} {u : B} (huW : ∀ v : V, u • v ∈ W) (hunit : IsUnit (lam u)) :
    eigen 𝒪 (V := V) lam ≤ W := by
  intro v hv
  obtain ⟨c, hc⟩ := hunit
  have h1 : v = (c⁻¹ : 𝒪ˣ) • (u • v) := by
    rw [hv u, ← hc]
    exact (inv_smul_smul c v).symm
  rw [h1]
  exact W.smul_mem _ (huW v)

theorem finrank_cornerSubmodule_eq (he : ∀ v : V, Sp.e i • v ∈ W) :
    Module.finrank 𝒪 ↥(cornerSubmodule (M := V) (Sp.e i)) =
      Module.finrank 𝒪 ↥(LinearMap.range (resAlg 𝒪 W hW (Sp.e i))) := by
  let f : ↥(cornerSubmodule (M := V) (Sp.e i)) →ₗ[𝒪] ↥(LinearMap.range (resAlg 𝒪 W hW (Sp.e i))) :=
    { toFun := fun x => ⟨⟨(x : V), by
          obtain ⟨y, hy⟩ := x.2
          rw [← hy]
          exact he y⟩, by
          obtain ⟨y, hy⟩ := x.2
          refine ⟨⟨Sp.e i • y, he y⟩, Subtype.ext ?_⟩
          simp only [coe_resAlg_apply]
          rw [← hy]
          show Sp.e i • Sp.e i • y = (Sp.e i • LinearMap.id (R := B)) y
          rw [smul_smul, (Sp.idem i).eq]
          rfl⟩
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : ↥(LinearMap.range (resAlg 𝒪 W hW (Sp.e i))) => ((z : W) : V)) hxy
  · rintro ⟨w, ⟨w0, rfl⟩⟩
    refine ⟨⟨Sp.e i • (w0 : V), ⟨(w0 : V), rfl⟩⟩, Subtype.ext (Subtype.ext rfl)⟩

variable (hfaith : ∀ b : B, (∀ v : V, b • v = 0) → b = 0)

include hfaith in

theorem e_mul_eq_zero_of_resAlg_eq_zero (he : ∀ v : V, Sp.e i • v ∈ W) {b : B}
    (hb : resAlg 𝒪 W hW b = 0) : Sp.e i * b = 0 := by
  apply hfaith
  intro v
  rw [mul_comm, mul_smul]
  have := congrArg (fun f : Module.End 𝒪 W => ((f ⟨Sp.e i • v, he v⟩ : W) : V)) hb
  simpa using this

include hfaith in

theorem finrank_cornerRing_eq (he : ∀ v : V, Sp.e i • v ∈ W) :
    Module.finrank 𝒪 (Sp.CornerRing i) =
      Module.finrank 𝒪 ↥(LinearMap.range (LinearMap.mulLeft 𝒪 (resAlg 𝒪 W hW (Sp.e i)) ∘ₗ
        (resAlg 𝒪 W hW).range.val.toLinearMap)) := by

  let val𝒪 : Sp.CornerRing i →ₗ[𝒪] B :=
    ((cornerSubmodule (M := B) (Sp.e i)).restrictScalars 𝒪).subtype ∘ₗ
      (Sp.cornerRingLinearEquiv i 𝒪).toLinearMap
  have hval𝒪 : ∀ z : Sp.CornerRing i, val𝒪 z = (z : B) := fun z => rfl
  let g : Sp.CornerRing i →ₗ[𝒪] Module.End 𝒪 W := (resAlg 𝒪 W hW).toLinearMap ∘ₗ val𝒪
  have hg : ∀ z : Sp.CornerRing i, g z = resAlg 𝒪 W hW (z : B) := fun z => rfl
  have hg_inj : Function.Injective g := by
    intro x y hxy
    rw [hg, hg] at hxy
    have h0 : resAlg 𝒪 W hW ((x : B) - (y : B)) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hxy
    have h1 := e_mul_eq_zero_of_resAlg_eq_zero 𝒪 Sp i W hW hfaith he h0
    rw [mul_sub, Sp.e_mul_coe, Sp.e_mul_coe, sub_eq_zero] at h1
    exact Subtype.ext h1
  have hg_range : LinearMap.range g =
      LinearMap.range (LinearMap.mulLeft 𝒪 (resAlg 𝒪 W hW (Sp.e i)) ∘ₗ
        (resAlg 𝒪 W hW).range.val.toLinearMap) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨⟨resAlg 𝒪 W hW (z : B), ⟨(z : B), rfl⟩⟩, ?_⟩
      rw [hg]
      show resAlg 𝒪 W hW (Sp.e i) * resAlg 𝒪 W hW (z : B) = resAlg 𝒪 W hW (z : B)
      rw [← map_mul, Sp.e_mul_coe]
    · rintro _ ⟨⟨_, ⟨b, rfl⟩⟩, rfl⟩
      refine ⟨Sp.toCornerRing i b, ?_⟩
      rw [hg]
      show resAlg 𝒪 W hW (Sp.e i * b * Sp.e i) = resAlg 𝒪 W hW (Sp.e i) * resAlg 𝒪 W hW b
      rw [mul_comm (Sp.e i) b, mul_assoc, (Sp.idem i).eq, mul_comm b, map_mul]
  rw [← hg_range]
  exact (LinearEquiv.ofInjective g hg_inj).finrank_eq

def lamB (πC : Sp.CornerRing i →ₐ[𝒪] 𝒪) : B →ₐ[𝒪] 𝒪 :=
  πC.comp (IsScalarTower.toAlgHom 𝒪 B (Sp.CornerRing i))

theorem lamB_apply (πC : Sp.CornerRing i →ₐ[𝒪] 𝒪) (b : B) :
    lamB 𝒪 Sp i πC b = πC (Sp.toCornerRing i b) := rfl

theorem lamB_e (πC : Sp.CornerRing i →ₐ[𝒪] 𝒪) : lamB 𝒪 Sp i πC (Sp.e i) = 1 := by
  rw [lamB_apply, toCornerRing_e, map_one]

theorem finrank_torsionBySet_eq (πC : Sp.CornerRing i →ₐ[𝒪] 𝒪) :
    Module.finrank 𝒪 ↥((Submodule.torsionBySet (Sp.CornerRing i)
        ↥(cornerSubmodule (M := V) (Sp.e i)) ↑(RingHom.ker πC)).restrictScalars 𝒪) =
      Module.finrank 𝒪 ↥(eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC)) := by

  have hcorner : ∀ v : V, v ∈ eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC) →
      v ∈ cornerSubmodule (M := V) (Sp.e i) := by
    intro v hv
    refine ⟨v, ?_⟩
    show Sp.e i • LinearMap.id (R := B) v = v
    rw [LinearMap.id_apply, hv (Sp.e i), lamB_e, one_smul]

  have htors : ∀ x : ↥(cornerSubmodule (M := V) (Sp.e i)),
      x ∈ Submodule.torsionBySet (Sp.CornerRing i) _ ↑(RingHom.ker πC) ↔
        (x : V) ∈ eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC) := by
    intro x
    rw [Submodule.mem_torsionBySet_iff, mem_eigen]
    constructor
    · intro h b

      have hk : Sp.toCornerRing i (b - algebraMap 𝒪 B (lamB 𝒪 Sp i πC b)) ∈ RingHom.ker πC := by
        rw [RingHom.mem_ker]
        show πC (Sp.toCornerRing i (b - algebraMap 𝒪 B (lamB 𝒪 Sp i πC b))) = 0
        rw [map_sub, map_sub, ← lamB_apply, toCornerRing_algebraMap, AlgHom.commutes]
        exact sub_self _
      have h1 := congrArg (fun y : ↥(cornerSubmodule (M := V) (Sp.e i)) => (y : V)) (h ⟨_, hk⟩)
      simp only [ZeroMemClass.coe_zero, IdempotentSplitting.coe_cornerSmul,
        IdempotentSplitting.coe_toCornerRing] at h1

      have hex : Sp.e i • (x : V) = x := Sp.e_smul_coe i x
      have h2 : (Sp.e i * (b - algebraMap 𝒪 B (lamB 𝒪 Sp i πC b)) * Sp.e i) • (x : V) =
          b • (x : V) - lamB 𝒪 Sp i πC b • (x : V) := by
        rw [mul_smul, hex, mul_comm, mul_smul, hex, sub_smul, algebraMap_smul]
      rw [h2, sub_eq_zero] at h1
      exact h1
    · rintro h ⟨c, hc⟩
      apply Subtype.ext
      simp only [IdempotentSplitting.coe_cornerSmul, ZeroMemClass.coe_zero]
      have h1 := h (c : B)
      have h2 : lamB 𝒪 Sp i πC (c : B) = 0 := by
        rw [lamB_apply]
        have : Sp.toCornerRing i (c : B) = c := by
          apply Subtype.ext
          show Sp.e i * (c : B) * Sp.e i = c
          rw [Sp.e_mul_coe, Sp.coe_mul_e]
        rw [this]
        exact hc
      rw [h1, h2, zero_smul]
  let f : ↥((Submodule.torsionBySet (Sp.CornerRing i)
        ↥(cornerSubmodule (M := V) (Sp.e i)) ↑(RingHom.ker πC)).restrictScalars 𝒪) →ₗ[𝒪]
      ↥(eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC)) :=
    { toFun := fun x => ⟨((x : ↥(cornerSubmodule (M := V) (Sp.e i))) : V), (htors _).mp x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  refine (LinearEquiv.ofBijective f ⟨?_, ?_⟩).finrank_eq
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC)) => (z : V)) hxy
  · rintro ⟨v, hv⟩
    exact ⟨⟨⟨v, hcorner v hv⟩, (htors _).mpr hv⟩, rfl⟩

include hfaith in

theorem lamB_eq_zero_of_resAlg_eq_zero (he : ∀ v : V, Sp.e i • v ∈ W)
    (πC : Sp.CornerRing i →ₐ[𝒪] 𝒪) {b : B} (hb : resAlg 𝒪 W hW b = 0) :
    lamB 𝒪 Sp i πC b = 0 := by
  have h1 := e_mul_eq_zero_of_resAlg_eq_zero 𝒪 Sp i W hW hfaith he hb
  rw [lamB_apply]
  have : Sp.toCornerRing i b = 0 := by
    apply Subtype.ext
    show Sp.e i * b * Sp.e i = ((0 : Sp.CornerRing i) : B)
    rw [h1, zero_mul]
    rfl
  rw [this, map_zero]

def lamA (he : ∀ v : V, Sp.e i • v ∈ W) (πC : Sp.CornerRing i →ₐ[𝒪] 𝒪) :
    ↥(resAlg 𝒪 W hW).range →ₐ[𝒪] 𝒪 :=
  (Ideal.Quotient.liftₐ (RingHom.ker (resAlg 𝒪 W hW)) (lamB 𝒪 Sp i πC)
      (fun b hb => lamB_eq_zero_of_resAlg_eq_zero 𝒪 Sp i W hW hfaith he πC
        ((RingHom.mem_ker).mp hb))).comp
    (Ideal.quotientKerEquivRange (resAlg 𝒪 W hW)).symm.toAlgHom

theorem lamA_apply (he : ∀ v : V, Sp.e i • v ∈ W) (πC : Sp.CornerRing i →ₐ[𝒪] 𝒪) (b : B) :
    lamA 𝒪 Sp i W hW hfaith he πC ⟨resAlg 𝒪 W hW b, ⟨b, rfl⟩⟩ = lamB 𝒪 Sp i πC b := by
  have h1 : (Ideal.quotientKerEquivRange (resAlg 𝒪 W hW)).symm ⟨resAlg 𝒪 W hW b, ⟨b, rfl⟩⟩ =
      Ideal.Quotient.mk (RingHom.ker (resAlg 𝒪 W hW)) b := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  unfold lamA
  rw [AlgHom.comp_apply]
  change Ideal.Quotient.liftₐ _ (lamB 𝒪 Sp i πC) _
    ((Ideal.quotientKerEquivRange (resAlg 𝒪 W hW)).symm ⟨resAlg 𝒪 W hW b, ⟨b, rfl⟩⟩) = _
  rw [h1]
  rfl

theorem finrank_eigen_eq (he : ∀ v : V, Sp.e i • v ∈ W) (πC : Sp.CornerRing i →ₐ[𝒪] 𝒪)
    (hle : eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC) ≤ W) :
    Module.finrank 𝒪 ↥(eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC)) =
      Module.finrank 𝒪 ↥(⨅ a : ↥(resAlg 𝒪 W hW).range,
        Module.End.eigenspace (a : Module.End 𝒪 W) (lamA 𝒪 Sp i W hW hfaith he πC a)) := by
  have hmem : ∀ w : W, w ∈ (⨅ a : ↥(resAlg 𝒪 W hW).range,
        Module.End.eigenspace (a : Module.End 𝒪 W) (lamA 𝒪 Sp i W hW hfaith he πC a)) ↔
      (w : V) ∈ eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC) := by
    intro w
    rw [Submodule.mem_iInf, mem_eigen]
    constructor
    · intro h b
      have h1 := h ⟨resAlg 𝒪 W hW b, ⟨b, rfl⟩⟩
      rw [Module.End.mem_eigenspace_iff, lamA_apply] at h1
      have h2 := congrArg (fun z : W => (z : V)) h1
      simpa using h2
    · intro h a
      obtain ⟨b, hb⟩ := a.2
      have ha : a = ⟨resAlg 𝒪 W hW b, ⟨b, rfl⟩⟩ := Subtype.ext hb.symm
      rw [ha, Module.End.mem_eigenspace_iff, lamA_apply]
      apply Subtype.ext
      simpa using h b
  let f : ↥(eigen 𝒪 (V := V) (lamB 𝒪 Sp i πC)) →ₗ[𝒪]
      ↥(⨅ a : ↥(resAlg 𝒪 W hW).range,
        Module.End.eigenspace (a : Module.End 𝒪 W) (lamA 𝒪 Sp i W hW hfaith he πC a)) :=
    { toFun := fun x => ⟨⟨(x : V), hle x.2⟩, (hmem _).mpr x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  refine (LinearEquiv.ofBijective f ⟨?_, ?_⟩).finrank_eq
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : ↥(⨅ a : ↥(resAlg 𝒪 W hW).range,
        Module.End.eigenspace (a : Module.End 𝒪 W) (lamA 𝒪 Sp i W hW hfaith he πC a)) => ((z : W) : V)) hxy
  · rintro ⟨w, hw⟩
    exact ⟨⟨(w : V), (hmem w).mp hw⟩, rfl⟩

end Module

section Transport

variable {R : Type*} [CommRing R] {Wm : Type*} [AddCommGroup Wm] [Module R Wm] {n : ℕ}
variable (bR : Basis (Fin n) R Wm)

abbrev Φm : Module.End R Wm ≃ₐ[R] Matrix (Fin n) (Fin n) R := LinearMap.toMatrixAlgEquiv bR

theorem Φm_apply (x : Module.End R Wm) : Φm bR x = LinearMap.toMatrix bR bR x := rfl

abbrev ΦmH : Module.End R Wm →ₐ[R] Matrix (Fin n) (Fin n) R :=
  (Φm bR : Module.End R Wm →ₐ[R] Matrix (Fin n) (Fin n) R)

@[scoped simp] theorem ΦmH_apply (x : Module.End R Wm) : ΦmH bR x = Φm bR x := rfl

theorem toLin'_Φm_apply (x : Module.End R Wm) (w : Wm) :
    Matrix.toLin' (Φm bR x) (bR.equivFun w) = bR.equivFun (x w) := by
  rw [Matrix.toLin'_apply, Φm_apply, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    LinearMap.toMatrix_mulVec_repr]

theorem toLin'_Φm_comp (x : Module.End R Wm) :
    Matrix.toLin' (Φm bR x) ∘ₗ (bR.equivFun : Wm →ₗ[R] (Fin n → R)) =
      (bR.equivFun : Wm →ₗ[R] (Fin n → R)) ∘ₗ x := by
  ext w
  exact congrFun (toLin'_Φm_apply bR x w) _

theorem finrank_range_toLin'_Φm (x : Module.End R Wm) :
    Module.finrank R ↥(LinearMap.range (Matrix.toLin' (Φm bR x))) =
      Module.finrank R ↥(LinearMap.range x) := by
  have h : LinearMap.range (Matrix.toLin' (Φm bR x)) =
      (LinearMap.range x).map (bR.equivFun : Wm →ₗ[R] (Fin n → R)) := by
    rw [LinearMap.range_eq_map x, ← Submodule.map_comp, ← toLin'_Φm_comp, Submodule.map_comp,
      Submodule.map_top, LinearEquiv.range, Submodule.map_top]
  rw [h]
  exact LinearEquiv.finrank_map_eq _ _

variable (A : Subalgebra R (Module.End R Wm))

theorem finrank_range_mulLeft_Φm (x : Module.End R Wm) :
    Module.finrank R ↥(LinearMap.range (LinearMap.mulLeft R (Φm bR x) ∘ₗ
        (A.map (ΦmH bR)).val.toLinearMap)) =
      Module.finrank R ↥(LinearMap.range (LinearMap.mulLeft R x ∘ₗ A.val.toLinearMap)) := by
  have h : LinearMap.range (LinearMap.mulLeft R (Φm bR x) ∘ₗ
        (A.map (ΦmH bR)).val.toLinearMap) =
      (LinearMap.range (LinearMap.mulLeft R x ∘ₗ A.val.toLinearMap)).map
        ((Φm bR).toLinearEquiv : Module.End R Wm →ₗ[R] Matrix (Fin n) (Fin n) R) := by
    apply le_antisymm
    · rintro _ ⟨⟨a', ha'⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Subalgebra.mem_map.mp ha'
      refine ⟨x * a, ⟨⟨a, ha⟩, rfl⟩, ?_⟩
      show Φm bR (x * a) = Φm bR x * Φm bR a
      rw [map_mul]
    · rintro _ ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
      refine ⟨⟨Φm bR a, Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
      show Φm bR x * Φm bR a = Φm bR (x * a)
      rw [map_mul]
  rw [h]
  exact LinearEquiv.finrank_map_eq _ _

abbrev idxEquiv : ↥A ≃ₐ[R] ↥(A.map (ΦmH bR)) :=
  (Φm bR).subalgebraMap A

theorem coe_idxEquiv (a : A) :
    ((idxEquiv bR A a : ↥(A.map (ΦmH bR))) :
      Matrix (Fin n) (Fin n) R) = Φm bR a :=
  AlgEquiv.subalgebraMap_apply_coe _ _ _

theorem finrank_iInf_eigenspace_Φm
    (g : ↥(A.map (ΦmH bR)) → R) :
    Module.finrank R ↥(⨅ a' : ↥(A.map (ΦmH bR)),
        Module.End.eigenspace (Matrix.toLin' (a' : Matrix (Fin n) (Fin n) R)) (g a')) =
      Module.finrank R ↥(⨅ a : A, Module.End.eigenspace (a : Module.End R Wm)
        (g (idxEquiv bR A a))) := by
  set E' := ⨅ a' : ↥(A.map (ΦmH bR)),
        Module.End.eigenspace (Matrix.toLin' (a' : Matrix (Fin n) (Fin n) R)) (g a') with hE'
  have hcomap : E'.comap (bR.equivFun : Wm →ₗ[R] (Fin n → R)) =
      ⨅ a : A, Module.End.eigenspace (a : Module.End R Wm) (g (idxEquiv bR A a)) := by
    rw [hE', Submodule.comap_iInf]
    rw [← Equiv.iInf_comp (idxEquiv bR A).toEquiv]
    refine iInf_congr fun a => ?_
    ext w
    simp only [Submodule.mem_comap, Module.End.mem_eigenspace_iff, AlgEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, coe_idxEquiv]
    change Matrix.toLin' (Φm bR a) (bR.equivFun w) = _ ↔ _
    rw [toLin'_Φm_apply, ← map_smul]
    exact bR.equivFun.injective.eq_iff
  rw [← hcomap, Submodule.comap_equiv_eq_map_symm]
  exact (LinearEquiv.finrank_map_eq _ _).symm

theorem exists_bijective_of_basis {d : ℕ} (β : Module.Basis (Fin d) A Wm) :
    ∃ v : Fin d → (Fin n → R), Function.Bijective
      (fun c : Fin d → ↥(A.map (ΦmH bR)) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) R).mulVec (v k))) := by
  refine ⟨fun k => bR.equivFun (β k), ?_⟩

  let e0 : (Fin d → ↥(A.map (ΦmH bR))) ≃ (Fin d → A) :=
    Equiv.arrowCongr (Equiv.refl _) (idxEquiv bR A).symm.toEquiv
  have hfac : (fun c : Fin d → ↥(A.map (ΦmH bR)) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) R).mulVec (bR.equivFun (β k)))) =
      (bR.equivFun : Wm → (Fin n → R)) ∘ (β.equivFun.symm : (Fin d → A) → Wm) ∘ e0 := by
    funext c
    simp only [Function.comp_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : ((c k : Matrix (Fin n) (Fin n) R)) = Φm bR ((idxEquiv bR A).symm (c k) : A) := by
      have := coe_idxEquiv bR A ((idxEquiv bR A).symm (c k))
      rw [AlgEquiv.apply_symm_apply] at this
      exact this
    rw [hk, ← Matrix.toLin'_apply, toLin'_Φm_apply]
    rfl
  rw [hfac]
  exact bR.equivFun.bijective.comp (β.equivFun.symm.bijective.comp e0.bijective)

end Transport

section Parabolic

open CongruenceSubgroup ModularCurve.Period
open scoped MatrixGroups

variable (N : ℕ) [NeZero N]

abbrev parR (R : Type) [CommRing R] : Submodule R (CohCarrier.H1 N ⊤ R) :=
  parabolicHoms R (CohCarrier.GammaH N ⊤) R

def eqv : ↥(CohCarrier.GammaH N ⊤) ≃* ↥(Gamma0 N) := MulEquiv.subgroupCongr CohCarrier.GammaH_top

theorem isParabolicHom_heckeT (ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    (φ : CohCarrier.H1 N ⊤ A) (hφ : IsParabolicHom (CohCarrier.GammaH N ⊤) φ) :
    IsParabolicHom (CohCarrier.GammaH N ⊤) (CohCarrier.heckeT N ⊤ ℓ A φ) := by
  let ψ : Additive ↥(Gamma0 N) →+ A := φ.comp (MonoidHom.toAdditive (eqv N).symm.toMonoidHom)
  have hφψ : ∀ γ : ↥(CohCarrier.GammaH N ⊤), φ (Additive.ofMul γ) =
      ψ (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) := by
    intro γ
    show φ (Additive.ofMul γ) = φ (Additive.ofMul ((eqv N).symm ⟨(γ : SL(2, ℤ)), _⟩))
    congr 2
  have hψ : IsParabolicHom (Gamma0 N) ψ := by
    intro δ hδ
    show φ (Additive.ofMul ((eqv N).symm δ)) = 0
    exact hφ ((eqv N).symm δ) hδ
  have hT := heckeOperatorHom_preserves_parabolic N ℓ A ψ hψ
  intro γ hγ
  rw [CohCarrier.heckeT_top_apply_eq_heckeOperatorHom N ℓ A φ ψ hφψ γ]
  exact hT ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩ hγ

theorem heckeT_mem_parR (R : Type) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (φ : CohCarrier.H1 N ⊤ R)
    (hφ : φ ∈ parR N R) : CohCarrier.heckeT N ⊤ ℓ R φ ∈ parR N R :=
  isParabolicHom_heckeT N ℓ φ hφ

def Tpar (R : Type) [CommRing R] (ℓ : ℕ) [NeZero ℓ] : Module.End R ↥(parR N R) :=
  (CohCarrier.heckeTL N ⊤ R ℓ).restrict fun φ hφ => heckeT_mem_parR N R ℓ φ hφ

@[scoped simp] theorem coe_Tpar (R : Type) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (φ : ↥(parR N R)) :
    ((Tpar N R ℓ φ : ↥(parR N R)) : CohCarrier.H1 N ⊤ R) = CohCarrier.heckeT N ⊤ ℓ R φ := rfl

theorem heckeT_comp_addMonoidHom (ℓ : ℕ) [NeZero ℓ] {A A' : Type*} [AddCommGroup A] [AddCommGroup A']
    (f : A →+ A') (φ : CohCarrier.H1 N ⊤ A) :
    CohCarrier.heckeT N ⊤ ℓ A' (f.comp φ) = f.comp (CohCarrier.heckeT N ⊤ ℓ A φ) := by
  refine AddMonoidHom.ext fun x => ?_
  simp only [CohCarrier.heckeT, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_comp,
    Function.comp_apply, MonoidHom.toAdditiveLeft_apply_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
    MonoidHom.coe_comp, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, map_sum]

abbrev Idx (S : Set ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S}

def TparI (S : Set ℕ) (R : Type) [CommRing R] (i : Idx S) : Module.End R ↥(parR N R) :=
  haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩
  Tpar N R i.1

def castPar (R : Type) [CommRing R] : ↥(parR N ℤ) →+ ↥(parR N R) where
  toFun φ := ⟨(Int.castAddHom R).comp (φ : CohCarrier.H1 N ⊤ ℤ), by
    intro γ hγ
    show (Int.castAddHom R) ((φ : CohCarrier.H1 N ⊤ ℤ) (Additive.ofMul γ)) = 0
    rw [φ.2 γ hγ, map_zero]⟩
  map_zero' := by ext; simp
  map_add' φ ψ := by ext; simp

theorem coe_castPar (R : Type) [CommRing R] (φ : ↥(parR N ℤ)) :
    ((castPar N R φ : ↥(parR N R)) : CohCarrier.H1 N ⊤ R) =
      (Int.castAddHom R).comp (φ : CohCarrier.H1 N ⊤ ℤ) := rfl

theorem castPar_TparI (S : Set ℕ) (R : Type) [CommRing R] (i : Idx S) (φ : ↥(parR N ℤ)) :
    castPar N R (TparI N S ℤ i φ) = TparI N S R i (castPar N R φ) := by
  haveI : NeZero i.1 := ⟨i.2.1.ne_zero⟩
  apply Subtype.ext
  show (Int.castAddHom R).comp (CohCarrier.heckeT N ⊤ i.1 ℤ φ) =
    CohCarrier.heckeT N ⊤ i.1 R ((Int.castAddHom R).comp (φ : CohCarrier.H1 N ⊤ ℤ))
  rw [heckeT_comp_addMonoidHom]

variable {N}
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR N ℤ))

def Mint (S : Set ℕ) (i : Idx S) : Matrix (Fin n) (Fin n) ℤ := LinearMap.toMatrix b b (TparI N S ℤ i)

variable {R : Type} [CommRing R] (bR : Module.Basis (Fin n) R ↥(parR N R))
  (hbR : ∀ i, (bR i : CohCarrier.H1 N ⊤ R) = (Int.castAddHom R).comp (b i : CohCarrier.H1 N ⊤ ℤ))

include hbR in
theorem castPar_b (j : Fin n) : castPar N R (b j) = bR j := Subtype.ext (hbR j).symm

include hbR in

theorem toMatrix_TparI (S : Set ℕ) (i : Idx S) :
    LinearMap.toMatrix bR bR (TparI N S R i) = (Mint b S i).map (Int.cast : ℤ → R) := by
  ext k j
  rw [LinearMap.toMatrix_apply, Matrix.map_apply, Mint]

  have hexp : TparI N S ℤ i (b j) = ∑ k, (LinearMap.toMatrix b b (TparI N S ℤ i) k j) • b k := by
    conv_lhs => rw [← b.sum_repr (TparI N S ℤ i (b j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.toMatrix_apply]
  have h1 : TparI N S R i (bR j) = ∑ k, ((LinearMap.toMatrix b b (TparI N S ℤ i) k j : ℤ) : R) • bR k := by
    rw [← castPar_b b bR hbR j, ← castPar_TparI, hexp, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, castPar_b b bR hbR k]
    exact (Int.cast_smul_eq_zsmul R _ _).symm
  rw [h1]
  have h2 : bR.repr (∑ k, ((LinearMap.toMatrix b b (TparI N S ℤ i) k j : ℤ) : R) • bR k) =
      Finsupp.equivFunOnFinite.symm fun k => ((LinearMap.toMatrix b b (TparI N S ℤ i) k j : ℤ) : R) := by
    rw [← Module.Basis.equivFun_symm_apply]
    apply bR.repr.symm.injective
    simp [Module.Basis.equivFun]
  rw [h2]
  rfl

include hbR in

theorem map_adjoin_TparI (S : Set ℕ) :
    (Algebra.adjoin R (Set.range (TparI N S R))).map
        (ΦmH bR) =
      Algebra.adjoin R (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → R)) := by
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  have h : (ΦmH bR : Module.End R ↥(parR N R) → Matrix (Fin n) (Fin n) R) ∘ TparI N S R =
      fun i => (Mint b S i).map (Int.cast : ℤ → R) := by
    funext i
    show Φm bR (TparI N S R i) = _
    rw [Φm_apply, toMatrix_TparI b bR hbR]
  rw [h]

end Parabolic

section OverC

open CongruenceSubgroup ModularCurve.Period

variable (N : ℕ) [NeZero N] (S : Set ℕ)

theorem genSet_eq (R : Type) [CommRing R] :
    {T : Module.End R ↥(parabolicHoms R (CohCarrier.GammaH N ⊤) R) |
        ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          ((T v : ↥(parabolicHoms R (CohCarrier.GammaH N ⊤) R)) : CohCarrier.H1 N ⊤ R) =
            CohCarrier.heckeT N ⊤ ℓ R (v : CohCarrier.H1 N ⊤ R)} =
      Set.range (TparI N S R) := by
  ext T
  constructor
  · rintro ⟨ℓ, hℓ, hℓS, h⟩
    refine ⟨⟨ℓ, hℓ, hℓS⟩, ?_⟩
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact (h v).symm
  · rintro ⟨⟨ℓ, hℓ, hℓS⟩, rfl⟩
    exact ⟨ℓ, hℓ, hℓS, fun v => rfl⟩

variable (hSfin : S.Finite) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S)
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ ↥(parR N ℤ))
  (bC : Module.Basis (Fin n) ℂ ↥(parR N ℂ))
  (hbC : ∀ i, (bC i : CohCarrier.H1 N ⊤ ℂ) = (Int.castAddHom ℂ).comp (b i : CohCarrier.H1 N ⊤ ℤ))

include hSfin hS hbC in
set_option maxHeartbeats 8000000 in

theorem descent_hypotheses :
    (∃ v : Fin 2 → (Fin n → ℂ), Function.Bijective
      (fun c : Fin 2 → ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))) =>
        ∑ k, ((c k : Matrix (Fin n) (Fin n) ℂ).mulVec (v k)))) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → ℂ))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) ℂ)) (χ a)) = 2 := by
  obtain ⟨⟨β⟩, hmult⟩ :=
    CohCarrier.nonempty_basis_fin_two_parabolicHoms_and_finrank_eigenspace_eq_two N S hSfin hS
  rw [genSet_eq N S ℂ] at β hmult
  have hmap := map_adjoin_TparI b bC hbC S
  rw [← hmap]
  refine ⟨exists_bijective_of_basis bC _ β, fun χ => ?_⟩
  rw [finrank_iInf_eigenspace_Φm bC (Algebra.adjoin ℂ (Set.range (TparI N S ℂ))) χ]
  exact hmult (χ.comp (idxEquiv bC (Algebra.adjoin ℂ (Set.range (TparI N S ℂ)))).toAlgHom)

include hSfin hS hbC in

theorem descent (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪] [CharZero 𝒪] :
    (∀ ε ∈ Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪)),
      IsIdempotentElem ε →
        Module.finrank 𝒪 ↥(LinearMap.range (Matrix.toLin' ε)) =
          2 * Module.finrank 𝒪 ↥(LinearMap.range (LinearMap.mulLeft 𝒪 ε ∘ₗ
            (Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪))).val.toLinearMap))) ∧
    ∀ lam : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪))) →ₐ[𝒪] 𝒪,
      Module.finrank 𝒪 ↥(⨅ a : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪))),
        Module.End.eigenspace (Matrix.toLin' (a : Matrix (Fin n) (Fin n) 𝒪)) (lam a)) = 2 := by
  obtain ⟨hfree, hmult⟩ := descent_hypotheses N S hSfin hS b bC hbC
  exact Matrix.finrank_range_and_eigenspace_of_adjoin_intCast n 2 (Mint b S) hfree hmult 𝒪

end OverC

section Assembly

open CongruenceSubgroup ModularCurve.Period CohCarrier
open scoped MatrixGroups IsMulCommutative

theorem diamondL_top_apply (N : ℕ) [NeZero N] (𝒪 : Type) [CommRing 𝒪] (d : (ZMod N)ˣ)
    (φ : CohCarrier.H1 N ⊤ 𝒪) : CohCarrier.diamondL N ⊤ 𝒪 d φ = φ := by
  set σ := Classical.choose (CohCarrier.gamma0Units_surjective N d) with hσdef
  rw [CohCarrier.diamondL_eq_diamondRaw N ⊤ 𝒪 d σ (Classical.choose_spec (CohCarrier.gamma0Units_surjective N d))]
  have hσ : (σ : SL(2, ℤ)) ∈ CohCarrier.GammaH N ⊤ := by
    rw [CohCarrier.GammaH_top]; exact σ.2
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (CohCarrier.conjHom N ⊤ σ (Additive.toMul x))) = φ x
  have hconj : CohCarrier.conjHom N ⊤ σ (Additive.toMul x) =
      ⟨(σ : SL(2, ℤ)), hσ⟩ * Additive.toMul x * ⟨(σ : SL(2, ℤ)), hσ⟩⁻¹ := Subtype.ext rfl
  rw [hconj, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  simp only [ofMul_toMul]
  abel

@[reducible] def cornerCommRing {B : Type} [CommRing B] (Sp : IdempotentSplitting B) (i : Fin Sp.n) :
    CommRing (Sp.CornerRing i) := inferInstance

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

variable (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 h =
        CohCarrier.opFamily N ⊤ S 𝒪 h * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)

abbrev TT : Type :=
  ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra

scoped instance : IsScalarTower 𝒪 (TT N S 𝒪 hcomm θbar) (CohCarrier.H1 N ⊤ 𝒪) :=
  ⟨fun r t v => rfl⟩

theorem TT_smul_def (t : TT N S 𝒪 hcomm θbar) (v : CohCarrier.H1 N ⊤ 𝒪) :
    t • v = (t : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) v := rfl

theorem TT_faithful (t : TT N S 𝒪 hcomm θbar) (h : ∀ v : CohCarrier.H1 N ⊤ 𝒪, t • v = 0) : t = 0 :=
  Subtype.ext (LinearMap.ext h)

abbrev gen (g : CohCarrier.Gen N S) : TT N S 𝒪 hcomm θbar :=
  ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
    Algebra.subset_adjoin (Set.mem_range_self g)⟩

theorem gen_apply_mem (g : CohCarrier.Gen N S) (v : CohCarrier.H1 N ⊤ 𝒪) (hv : v ∈ parR N 𝒪) :
    (CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g v ∈ parR N 𝒪 := by
  show CohCarrier.opFamily N ⊤ S 𝒪 g v ∈ parR N 𝒪
  cases g with
  | T ℓ hℓ hℓS hℓM =>
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact heckeT_mem_parR N 𝒪 ℓ v hv
  | U q hq hqM =>
      haveI : NeZero q := ⟨hq.ne_zero⟩
      exact heckeT_mem_parR N 𝒪 q v hv
  | dia d =>
      show CohCarrier.diamondL N ⊤ 𝒪 d v ∈ parR N 𝒪
      rw [diamondL_top_apply]
      exact hv

theorem TT_smul_mem (t : TT N S 𝒪 hcomm θbar) (v : CohCarrier.H1 N ⊤ 𝒪) (hv : v ∈ parR N 𝒪) :
    t • v ∈ parR N 𝒪 := by
  rw [TT_smul_def]
  have ht : (t : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) ∈ Algebra.adjoin 𝒪
      (Set.range (CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op) := t.2
  revert v
  refine Algebra.adjoin_induction (p := fun x _ => ∀ v : CohCarrier.H1 N ⊤ 𝒪, v ∈ parR N 𝒪 →
      x v ∈ parR N 𝒪) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨g, rfl⟩ v hv
    exact gen_apply_mem N S 𝒪 hcomm θbar g v hv
  · intro r v hv
    rw [Module.algebraMap_end_apply]
    exact (parR N 𝒪).smul_mem r hv
  · intro x y _ _ hx hy v hv
    rw [LinearMap.add_apply]
    exact (parR N 𝒪).add_mem (hx v hv) (hy v hv)
  · intro x y _ _ hx hy v hv
    rw [Module.End.mul_apply]
    exact hx _ (hy v hv)

abbrev res :=
  resAlg 𝒪 (B := TT N S 𝒪 hcomm θbar) (parR N 𝒪) (TT_smul_mem N S 𝒪 hcomm θbar)

theorem coe_res_apply (t : TT N S 𝒪 hcomm θbar) (w : ↥(parR N 𝒪)) :
    ((res N S 𝒪 hcomm θbar t w : ↥(parR N 𝒪)) : CohCarrier.H1 N ⊤ 𝒪) =
      (t : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) w := rfl

include hS in

theorem range_res : (res N S 𝒪 hcomm θbar).range = Algebra.adjoin 𝒪 (Set.range (TparI N S 𝒪)) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    have ht : (t : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) ∈ Algebra.adjoin 𝒪
        (Set.range (CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op) := t.2
    have key : ∀ (x : Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) (hx : x ∈ Algebra.adjoin 𝒪
        (Set.range (CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op)),
        res N S 𝒪 hcomm θbar ⟨x, hx⟩ ∈ Algebra.adjoin 𝒪 (Set.range (TparI N S 𝒪)) := by
      intro x hx
      refine Algebra.adjoin_induction (p := fun x hx => res N S 𝒪 hcomm θbar ⟨x, hx⟩ ∈
        Algebra.adjoin 𝒪 (Set.range (TparI N S 𝒪))) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨g, rfl⟩
        cases g with
        | T ℓ hℓ hℓS hℓM =>
            refine Algebra.subset_adjoin ⟨⟨ℓ, hℓ, hℓS⟩, ?_⟩
            exact LinearMap.ext fun w => Subtype.ext rfl
        | U q hq hqM =>
            refine Algebra.subset_adjoin ⟨⟨q, hq, hS q hq hqM⟩, ?_⟩
            exact LinearMap.ext fun w => Subtype.ext rfl
        | dia d =>
            have h1 : res N S 𝒪 hcomm θbar ⟨_, Algebra.subset_adjoin (Set.mem_range_self (Gen.dia d))⟩ = 1 := by
              refine LinearMap.ext fun w => Subtype.ext ?_
              show CohCarrier.diamondL N ⊤ 𝒪 d (w : CohCarrier.H1 N ⊤ 𝒪) = w
              exact diamondL_top_apply N 𝒪 d w
            rw [h1]
            exact Subalgebra.one_mem _
      · intro r
        have h1 : res N S 𝒪 hcomm θbar ⟨algebraMap 𝒪 _ r, Subalgebra.algebraMap_mem _ r⟩ =
            algebraMap 𝒪 _ r := (res N S 𝒪 hcomm θbar).commutes r
        rw [h1]
        exact Subalgebra.algebraMap_mem _ r
      · intro x y hx hy hpx hpy
        have h1 : res N S 𝒪 hcomm θbar ⟨x + y, Subalgebra.add_mem _ hx hy⟩ =
            res N S 𝒪 hcomm θbar ⟨x, hx⟩ + res N S 𝒪 hcomm θbar ⟨y, hy⟩ :=
          (map_add (res N S 𝒪 hcomm θbar) ⟨x, hx⟩ ⟨y, hy⟩)
        rw [h1]
        exact Subalgebra.add_mem _ hpx hpy
      · intro x y hx hy hpx hpy
        have h1 : res N S 𝒪 hcomm θbar ⟨x * y, Subalgebra.mul_mem _ hx hy⟩ =
            res N S 𝒪 hcomm θbar ⟨x, hx⟩ * res N S 𝒪 hcomm θbar ⟨y, hy⟩ :=
          (map_mul (res N S 𝒪 hcomm θbar) ⟨x, hx⟩ ⟨y, hy⟩)
        rw [h1]
        exact Subalgebra.mul_mem _ hpx hpy
    exact key t.1 ht
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨ℓ, hℓ, hℓS⟩, rfl⟩
    by_cases hℓN : ℓ ∣ N
    · refine ⟨gen N S 𝒪 hcomm θbar (Gen.U ℓ hℓ hℓN), ?_⟩
      exact LinearMap.ext fun w => Subtype.ext rfl
    · refine ⟨gen N S 𝒪 hcomm θbar (Gen.T ℓ hℓ hℓS hℓN), ?_⟩
      exact LinearMap.ext fun w => Subtype.ext rfl

variable (Sp : IharaLemma.IdempotentSplitting (TT N S 𝒪 hcomm θbar))
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), ℓ ≡ 1 [MOD N] ∧
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN) ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1)

theorem residue_surj : Function.Surjective (algebraMap 𝒪 (IsLocalRing.ResidueField 𝒪)) := by
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  exact IsLocalRing.residue_surjective

include hπk hEis in

theorem exists_nonEisenstein_elt :
    ∃ u : TT N S 𝒪 hcomm θbar, u ∉ Sp.𝔪 i₀ ∧ (∀ v : CohCarrier.H1 N ⊤ 𝒪, u • v ∈ parR N 𝒪) ∧
      ∀ πC : Sp.CornerRing i₀ →ₐ[𝒪] 𝒪, IsUnit (lamB 𝒪 Sp i₀ πC u) := by
  obtain ⟨ℓ, hℓ, hℓS, hℓN, h1, hne⟩ := hEis
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  letI : CommRing (Sp.CornerRing i₀) := cornerCommRing Sp i₀
  let u : TT N S 𝒪 hcomm θbar :=
    gen N S 𝒪 hcomm θbar (Gen.T ℓ hℓ hℓS hℓN) - algebraMap 𝒪 (TT N S 𝒪 hcomm θbar) ((ℓ : 𝒪) + 1)

  have hval : πk (Sp.toCornerRing i₀ u) = θbar (Gen.T ℓ hℓ hℓS hℓN) - ((ℓ : IsLocalRing.ResidueField 𝒪) + 1) := by
    show πk (Sp.toCornerRing i₀ (gen N S 𝒪 hcomm θbar (Gen.T ℓ hℓ hℓS hℓN) -
      algebraMap 𝒪 (TT N S 𝒪 hcomm θbar) ((ℓ : 𝒪) + 1))) = _
    rw [map_sub (Sp.toCornerRing i₀), map_sub πk, hπk, toCornerRing_algebraMap, AlgHom.commutes,
      map_add, map_natCast, map_one]
  have hval_ne : πk (Sp.toCornerRing i₀ u) ≠ 0 := by
    rw [hval]
    exact sub_ne_zero.mpr hne
  refine ⟨u, ?_, ?_, ?_⟩
  ·
    rw [𝔪_eq_ker Sp i₀ (residue_surj 𝒪) πk, RingHom.mem_ker]
    exact hval_ne
  ·
    intro v
    have hmem := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one N 𝒪 v ℓ hℓ hℓN
      (fun t ht => h1.of_dvd ((dvd_mul_right t t).trans ht))
    have huv : u • v = CohCarrier.heckeT N ⊤ ℓ 𝒪 v - (ℓ + 1) • v := by
      show ((gen N S 𝒪 hcomm θbar (Gen.T ℓ hℓ hℓS hℓN) -
        algebraMap 𝒪 (TT N S 𝒪 hcomm θbar) ((ℓ : 𝒪) + 1) : TT N S 𝒪 hcomm θbar) :
          Module.End 𝒪 (CohCarrier.H1 N ⊤ 𝒪)) v = _
      rw [Subalgebra.coe_sub, Subalgebra.coe_algebraMap, LinearMap.sub_apply,
        Module.algebraMap_end_apply, add_smul, one_smul, Nat.cast_smul_eq_nsmul, add_smul, one_smul]
      rfl
    rw [huv]
    exact hmem
  · intro πC

    have hagree : (Algebra.ofId 𝒪 (IsLocalRing.ResidueField 𝒪)).comp πC = πk :=
      algHom_eq_of_isLocalRing (residue_surj 𝒪) _ _
    have hres : IsLocalRing.residue 𝒪 (πC (Sp.toCornerRing i₀ u)) ≠ 0 := by
      have := congrArg (fun f => f (Sp.toCornerRing i₀ u)) hagree
      simp only [AlgHom.comp_apply, Algebra.ofId_apply, IsLocalRing.ResidueField.algebraMap_eq] at this
      rw [this]
      exact hval_ne
    rw [lamB_apply]
    by_contra hnu
    apply hres
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hnu

include hSfin hS hπk hEis in

theorem main :
    Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) =
      2 * Module.finrank 𝒪 (Sp.CornerRing i₀) ∧
    ∀ πC : Sp.CornerRing i₀ →ₐ[𝒪] 𝒪,
      Module.finrank 𝒪 ↥((Submodule.torsionBySet (Sp.CornerRing i₀)
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))
          ↑(RingHom.ker πC)).restrictScalars 𝒪) = 2 := by

  obtain ⟨b, hb⟩ := CohCarrier.exists_basis_parabolicHoms_top_two_mul_finrank N
  obtain ⟨b𝒪, hb𝒪⟩ := hb 𝒪
  obtain ⟨bC, hbC⟩ := hb ℂ

  obtain ⟨hD1, hD2⟩ := descent N S hSfin hS b bC hbC 𝒪

  obtain ⟨u, hu, huW, hunit⟩ := exists_nonEisenstein_elt N S 𝒪 hcomm θbar Sp i₀ πk hπk hEis
  have hW := TT_smul_mem N S 𝒪 hcomm θbar
  have hfaith := TT_faithful N S 𝒪 hcomm θbar
  have he : ∀ v : CohCarrier.H1 N ⊤ 𝒪, Sp.e i₀ • v ∈ parR N 𝒪 :=
    e_smul_mem 𝒪 Sp i₀ (parR N 𝒪) hW hu huW

  set A : Subalgebra 𝒪 (Module.End 𝒪 ↥(parR N 𝒪)) := (res N S 𝒪 hcomm θbar).range with hAdef
  have hAmat : A.map (ΦmH b𝒪) =
      Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪)) := by
    rw [hAdef, range_res N S hS 𝒪 hcomm θbar]
    exact map_adjoin_TparI b b𝒪 hb𝒪 S
  refine ⟨?_, fun πC => ?_⟩
  ·
    have hc := finrank_cornerSubmodule_eq 𝒪 Sp i₀ (parR N 𝒪) hW he
    have hr := finrank_cornerRing_eq 𝒪 Sp i₀ (parR N 𝒪) hW hfaith he
    set x : Module.End 𝒪 ↥(parR N 𝒪) := res N S 𝒪 hcomm θbar (Sp.e i₀) with hxdef
    have hxA : x ∈ A := ⟨Sp.e i₀, rfl⟩
    have hxmem : Φm b𝒪 x ∈ Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪)) := by
      rw [← hAmat]
      exact Subalgebra.mem_map.mpr ⟨x, hxA, rfl⟩
    have hxidem : IsIdempotentElem (Φm b𝒪 x) := by
      have : IsIdempotentElem x := by
        show x * x = x
        rw [hxdef, ← map_mul, (Sp.idem i₀).eq]
      exact this.map _
    have h1 := hD1 _ hxmem hxidem
    rw [← hAmat, finrank_range_toLin'_Φm, finrank_range_mulLeft_Φm] at h1
    exact hc.trans (h1.trans (by rw [hr]))
  ·
    have ht := finrank_torsionBySet_eq 𝒪 Sp i₀ (V := CohCarrier.H1 N ⊤ 𝒪) πC
    have hle : eigen 𝒪 (V := CohCarrier.H1 N ⊤ 𝒪) (lamB 𝒪 Sp i₀ πC) ≤ parR N 𝒪 :=
      eigen_le 𝒪 (parR N 𝒪) huW (hunit πC)
    have heig := finrank_eigen_eq 𝒪 Sp i₀ (parR N 𝒪) hW hfaith he πC hle

    let g : ↥(A.map (ΦmH b𝒪)) → 𝒪 := fun a' =>
      lamA 𝒪 Sp i₀ (parR N 𝒪) hW hfaith he πC ((idxEquiv b𝒪 A).symm a')
    have hT3 := finrank_iInf_eigenspace_Φm b𝒪 A g
    have hg : ∀ a : A, g (idxEquiv b𝒪 A a) = lamA 𝒪 Sp i₀ (parR N 𝒪) hW hfaith he πC a := fun a => by
      simp only [g, AlgEquiv.symm_apply_apply]
    have hX : (⨅ a : A, Module.End.eigenspace (a : Module.End 𝒪 ↥(parR N 𝒪)) (g (idxEquiv b𝒪 A a))) =
        ⨅ a : A, Module.End.eigenspace (a : Module.End 𝒪 ↥(parR N 𝒪))
          (lamA 𝒪 Sp i₀ (parR N 𝒪) hW hfaith he πC a) :=
      iInf_congr fun a => by rw [hg]
    rw [hX] at hT3

    let e2 : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪))) ≃ₐ[𝒪]
        ↥(A.map (ΦmH b𝒪)) := Subalgebra.equivOfEq _ _ hAmat.symm
    let lamH : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪))) →ₐ[𝒪] 𝒪 :=
      ((lamA 𝒪 Sp i₀ (parR N 𝒪) hW hfaith he πC).comp (idxEquiv b𝒪 A).symm.toAlgHom).comp e2.toAlgHom
    have h2 := hD2 lamH
    have hre : (⨅ a'' : ↥(Algebra.adjoin 𝒪 (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪))),
        Module.End.eigenspace (Matrix.toLin' a''.1) (lamH a'')) =
        ⨅ a' : ↥(A.map (ΦmH b𝒪)),
          Module.End.eigenspace (Matrix.toLin' a'.1) (g a') := by
      rw [← Equiv.iInf_comp e2.symm.toEquiv]
      refine iInf_congr fun a' => ?_
      have hval : (e2.symm.toEquiv a' : ↥(Algebra.adjoin 𝒪
          (Set.range fun i => (Mint b S i).map (Int.cast : ℤ → 𝒪)))).1 = a'.1 := rfl
      have hlam : lamH (e2.symm.toEquiv a') = g a' := by
        show lamA 𝒪 Sp i₀ (parR N 𝒪) hW hfaith he πC ((idxEquiv b𝒪 A).symm (e2 (e2.symm a'))) = _
        rw [AlgEquiv.apply_symm_apply]
      rw [hval, hlam]
    rw [hre] at h2
    exact ht.trans (heig.trans (hT3.symm.trans h2))

end Assembly

end ESD3
p2m_reactivate "P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein.ESD3"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
open scoped IsMulCommutative in
theorem solution
    (N : ℕ) [NeZero N] (S : Set ℕ) (hSfin : S.Finite) (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∉ S)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CharZero 𝒪]
    (hcomm : ∀ g h : CohCarrier.Gen N S,
      CohCarrier.opFamily N ⊤ S 𝒪 g * CohCarrier.opFamily N ⊤ S 𝒪 h =
        CohCarrier.opFamily N ⊤ S 𝒪 h * CohCarrier.opFamily N ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen N S → IsLocalRing.ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] IsLocalRing.ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen N S, πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata N ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N), ℓ ≡ 1 [MOD N] ∧
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN) ≠ (ℓ : IsLocalRing.ResidueField 𝒪) + 1) :
    Module.finrank 𝒪 ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀)) =
      2 * Module.finrank 𝒪 (Sp.CornerRing i₀) ∧
    ∀ πC : Sp.CornerRing i₀ →ₐ[𝒪] 𝒪,
      Module.finrank 𝒪 ↥((Submodule.torsionBySet (Sp.CornerRing i₀)
          ↥(IharaLemma.cornerSubmodule (M := CohCarrier.H1 N ⊤ 𝒪) (Sp.e i₀))
          ↑(RingHom.ker πC)).restrictScalars 𝒪) = 2 :=
  ESD3.main N S hSfin hS 𝒪 hcomm θbar Sp i₀ πk hπk hEis

end
p2m_reactivate "P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein.ESD3"

end S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein
end P2MW
export P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein (solution)

-- Prove2me | solution 1 for CohCarrier.exists_mvPolynomial_heckeT_eigenvalue_of_mem_parabolicHoms_gammaH_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f4f1b3e1-2c80-58c1-88a8-feacede83d17

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_Newforms
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Theorems.Thm_CohCarrier_mem_adjoin_heckeT_parabolicHoms_gammaH_top_of_finite
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_heckeT_mem_parabolicHoms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_mvPolynomial_heckeT_eigenvalue_of_mem_parabolicHoms_gammaH_top
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one"
p2m_attr_erase "simp" "ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply"
p2m_attr_erase "simp" "CohCarrier.HeckeData.mk.injEq"

set_option autoImplicit false

open CohCarrier ModularCurve.Period
open scoped MatrixGroups

namespace C2aSol

theorem mem_span_rat_of_mem_span_complex {m ι : Type} [Fintype m] [DecidableEq m]
    (u : ι → m → ℚ) (y : m → ℚ)
    (h : (fun k => ((y k : ℚ) : ℂ)) ∈
      Submodule.span ℂ (Set.range fun i => fun k => ((u i k : ℚ) : ℂ))) :
    y ∈ Submodule.span ℚ (Set.range u) := by
  classical
  by_contra hy
  obtain ⟨f, hfy, hfU⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  let w : m → ℚ := fun k => f fun j => if k = j then 1 else 0
  let F : (m → ℂ) →ₗ[ℂ] ℂ := ∑ k, ((w k : ℚ) : ℂ) • LinearMap.proj k
  have hF : ∀ v : m → ℚ, F (fun k => ((v k : ℚ) : ℂ)) = ((f v : ℚ) : ℂ) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v, Rat.cast_sum]
    simp only [F, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul, Rat.cast_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hF0 : ∀ i, F (fun k => ((u i k : ℚ) : ℂ)) = 0 := by
    intro i
    have hfi : f (u i) = 0 := by
      have hmem : f (u i) ∈ (Submodule.span ℚ (Set.range u)).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
      rw [hfU] at hmem
      exact (Submodule.mem_bot ℚ).mp hmem
    rw [hF, hfi, Rat.cast_zero]
  have hker : Submodule.span ℂ (Set.range fun i => fun k => ((u i k : ℚ) : ℂ)) ≤ LinearMap.ker F := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hF0 i)
  have h0 := hker h
  rw [LinearMap.mem_ker, hF] at h0
  exact hfy (by exact_mod_cast h0)

theorem exists_nsmul_eq_sum_of_mem_span_map {n : ℕ} {ι : Type} (U : ι → Matrix (Fin n) (Fin n) ℤ)
    (Y : Matrix (Fin n) (Fin n) ℤ)
    (h : Y.map (Int.cast : ℤ → ℂ) ∈ Submodule.span ℂ (Set.range fun i => (U i).map (Int.cast : ℤ → ℂ))) :
    ∃ (N : ℕ) (_ : N ≠ 0) (s : Finset ι) (z : ι → ℤ), N • Y = ∑ i ∈ s, z i • U i := by
  classical

  let fl : {R : Type} → Matrix (Fin n) (Fin n) R → (Fin n × Fin n → R) := fun A ij => A ij.1 ij.2
  have hflin : IsLinearMap ℂ (fl (R := ℂ)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have h1 : (fun k => (((fl Y k : ℤ) : ℚ) : ℂ)) ∈
      Submodule.span ℂ (Set.range fun i => fun k => (((fl (U i) k : ℤ) : ℚ) : ℂ)) := by
    have himg := Submodule.mem_map_of_mem (f := hflin.mk' _) h
    rw [Submodule.map_span, ← Set.range_comp] at himg
    convert himg using 2
    rfl
    rfl
  have h2 := mem_span_rat_of_mem_span_complex (fun i k => ((fl (U i) k : ℤ) : ℚ)) (fun k => ((fl Y k : ℤ) : ℚ)) h1
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp h2

  refine ⟨∏ i ∈ c.support, (c i).den, Finset.prod_ne_zero_iff.mpr fun i _ => (c i).den_nz, c.support,
    fun i => (c i).num * ∏ j ∈ c.support.erase i, ((c j).den : ℤ), ?_⟩
  ext a b
  have hq := congrFun hc (a, b)
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hq

  have key : ((∏ i ∈ c.support, (c i).den : ℕ) : ℚ) * (Y a b : ℚ) =
      ∑ i ∈ c.support, (((c i).num * ∏ j ∈ c.support.erase i, ((c j).den : ℤ) : ℤ) : ℚ) * (U i a b : ℚ) := by
    rw [← hq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← mul_assoc]
    congr 1
    rw [← Finset.mul_prod_erase c.support (fun j => (c j).den) hi]
    push_cast
    rw [mul_comm ((c i).den : ℚ), mul_assoc, mul_comm ((c i).den : ℚ), Rat.mul_den_eq_num]
    ring
  have key' : (((∏ i ∈ c.support, (c i).den : ℕ) : ℤ) * Y a b : ℤ) =
      ∑ i ∈ c.support, ((c i).num * ∏ j ∈ c.support.erase i, ((c j).den : ℤ)) * U i a b := by
    exact_mod_cast key
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  simp only [nsmul_eq_mul, smul_eq_mul]
  exact_mod_cast key'

end C2aSol

namespace C2aSol

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem heckeT_smul {A : Type} [CommRing A] (ℓ : ℕ) [NeZero ℓ] (c : A) (φ : H1 M H A) :
    heckeT M H ℓ A (c • φ) = c • heckeT M H ℓ A φ := by
  have h1 : ∀ ψ : H1 M H A, c • ψ = (AddMonoidHom.mulLeft c).comp ψ := fun ψ => by ext x; rfl
  rw [h1, h1, CohCarrier.heckeT_comp_coeff]

noncomputable def TL (A : Type) [CommRing A] (ℓ : ℕ) [NeZero ℓ] : H1 M H A →ₗ[A] H1 M H A where
  toFun := heckeT M H ℓ A
  map_add' := map_add _
  map_smul' := heckeT_smul M H ℓ

@[scoped simp] theorem TL_apply (A : Type) [CommRing A] (ℓ : ℕ) [NeZero ℓ] (φ : H1 M H A) :
    TL M H A ℓ φ = heckeT M H ℓ A φ := rfl

variable (I : Type) (val : I → ℕ) (hval : ∀ i, NeZero (val i))

noncomputable def TwL (A : Type) [CommRing A] : List I → (H1 M H A →ₗ[A] H1 M H A)
  | [] => LinearMap.id
  | i :: l => (haveI := hval i; TL M H A (val i)) ∘ₗ TwL A l

theorem TwL_nil (A : Type) [CommRing A] : TwL M H I val hval A [] = LinearMap.id := rfl
theorem TwL_cons (A : Type) [CommRing A] (i : I) (l : List I) :
    TwL M H I val hval A (i :: l) = (haveI := hval i; TL M H A (val i)) ∘ₗ TwL M H I val hval A l := rfl

theorem TwL_eigen (A : Type) [CommRing A] (φ : H1 M H A) (a : I → A)
    (h : ∀ i, haveI := hval i; heckeT M H (val i) A φ = a i • φ) (l : List I) :
    TwL M H I val hval A l φ = (l.map a).prod • φ := by
  induction l with
  | nil => simp [TwL_nil]
  | cons i l ih =>
    rw [TwL_cons, LinearMap.comp_apply, ih, List.map_cons, List.prod_cons]
    haveI := hval i
    rw [TL_apply, heckeT_smul, h i, smul_smul, mul_comm]

end C2aSol
p2m_reactivate "P2MW.S_CohCarrier_exists_mvPolynomial_heckeT_eigenvalue_of_mem_parabolicHoms_gammaH_top.C2aSol"

set_option maxHeartbeats 3200000 in
open C2aSol in
theorem C2aSol.main
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hS : S.Finite)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M)
    (hC2aC : ∀ (Tp : Module.End ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)),
      (∀ v, haveI : NeZero p := ⟨hp.ne_zero⟩;
      ((Tp v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) : CohCarrier.H1 M H ℂ) =
        CohCarrier.heckeT M H p ℂ (v : CohCarrier.H1 M H ℂ)) →
    Tp ∈ Algebra.adjoin ℂ {T : Module.End ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
      ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ ¬ ℓ ∣ M ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) : CohCarrier.H1 M H ℂ) =
          CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)}) :
    ∃ (n : ℕ) (_ : n ≠ 0) (P : MvPolynomial {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M} ℤ),
      ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A]
        (φ : CohCarrier.H1 M H A)
        (_ : φ ∈ ModularCurve.Period.parabolicHoms A (CohCarrier.GammaH M H) A) (_ : φ ≠ 0)
        (a : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M} → A) (b : A),
        (∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M}, haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩;
          CohCarrier.heckeT M H ℓ.1 A φ = a ℓ • φ) →
        (haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeT M H p A φ = b • φ) →
        (n : A) * b = MvPolynomial.aeval a P := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩

  set I := {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M} with hI
  let val : I → ℕ := fun ℓ => ℓ.1
  have hval : ∀ i : I, NeZero (val i) := fun i => ⟨i.2.1.ne_zero⟩

  set Γ := CohCarrier.GammaH M H with hΓ
  haveI : Γ.FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := CongruenceSubgroup.Gamma1 M) (fun A hA => ?_)
    obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem M A).mp hA
    rw [hΓ, CohCarrier.mem_GammaH_iff]
    refine ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
    have h1 : CohCarrier.gamma0Units M ⟨A, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 :=
      Units.ext (by rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11)
    rw [h1]
    exact H.one_mem
  obtain ⟨n₀, bZ, hb'⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree Γ
  have hb : ∀ (R : Type) [CommRing R] [IsAddTorsionFree R],
      ∃ bR : Module.Basis (Fin n₀) R (parabolicHoms R Γ R),
        ∀ i, (bR i : Additive Γ →+ R) = (Int.castAddHom R).comp (bZ i : Additive Γ →+ ℤ) :=
    fun R _ _ => hb' R
  clear hb'

  have hTpar : ∀ (A : Type) [AddCommGroup A] (ℓ : ℕ) [NeZero ℓ] (φ : H1 M H A),
      φ ∈ parabolicHoms ℤ Γ A → heckeT M H ℓ A φ ∈ parabolicHoms ℤ Γ A :=
    fun A _ ℓ _ φ hφ => CohCarrier.heckeT_mem_parabolicHoms M H A ℓ φ hφ
  let Bmat : ∀ (ℓ : ℕ) [NeZero ℓ], Matrix (Fin n₀) (Fin n₀) ℤ := fun ℓ _ i j =>
    bZ.repr ⟨heckeT M H ℓ ℤ (bZ j : H1 M H ℤ), hTpar ℤ ℓ _ (bZ j).2⟩ i
  have hBZ : ∀ (ℓ : ℕ) [NeZero ℓ] (j : Fin n₀),
      heckeT M H ℓ ℤ (bZ j : H1 M H ℤ) = ∑ i, Bmat ℓ i j • (bZ i : H1 M H ℤ) := by
    intro ℓ _ j
    have h := bZ.sum_repr ⟨heckeT M H ℓ ℤ (bZ j : H1 M H ℤ), hTpar ℤ ℓ _ (bZ j).2⟩
    have h' := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h'
    exact h'.symm

  have hBA : ∀ (A : Type) [CommRing A] [IsAddTorsionFree A]
      (bA : Module.Basis (Fin n₀) A (parabolicHoms A Γ A))
      (hbA : ∀ i, (bA i : Additive Γ →+ A) = (Int.castAddHom A).comp (bZ i : Additive Γ →+ ℤ))
      (ℓ : ℕ) [NeZero ℓ] (j : Fin n₀),
      heckeT M H ℓ A (bA j : H1 M H A) = ∑ i, (Bmat ℓ i j : A) • (bA i : H1 M H A) := by
    intro A _ _ bA hbA ℓ _ j
    have h1 : (bA j : H1 M H A) = (Int.castAddHom A).comp (bZ j : Additive Γ →+ ℤ) := hbA j
    rw [h1, CohCarrier.heckeT_comp_coeff, hBZ]
    refine AddMonoidHom.ext fun γ => ?_
    rw [AddMonoidHom.comp_apply, AddMonoidHom.finset_sum_apply, AddMonoidHom.finset_sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbA i]
    simp

  let Bw : List I → Matrix (Fin n₀) (Fin n₀) ℤ := fun l => (l.map fun ℓ => @Bmat ℓ.1 (hval ℓ)).prod
  have hBwA : ∀ (A : Type) [CommRing A] [IsAddTorsionFree A]
      (bA : Module.Basis (Fin n₀) A (parabolicHoms A Γ A))
      (hbA : ∀ i, (bA i : Additive Γ →+ A) = (Int.castAddHom A).comp (bZ i : Additive Γ →+ ℤ))
      (l : List I) (j : Fin n₀),
      TwL M H I val hval A l (bA j : H1 M H A) = ∑ i, (Bw l i j : A) • (bA i : H1 M H A) := by
    intro A _ _ bA hbA l
    induction l with
    | nil =>
      intro j
      have hBw0 : Bw [] = 1 := by simp only [Bw, List.map_nil, List.prod_nil]
      rw [TwL_nil, LinearMap.id_apply, hBw0, Finset.sum_eq_single j]
      · simp [Matrix.one_apply_eq]
      · intro i _ hij; simp [Matrix.one_apply_ne hij]
      · intro h; exact absurd (Finset.mem_univ j) h
    | cons ℓ l ih =>
      intro j
      haveI := hval ℓ
      rw [TwL_cons, LinearMap.comp_apply, ih, map_sum]
      simp only [map_smul, TL_apply]
      have : Bw (ℓ :: l) = Bmat (val ℓ) * Bw l := by
        simp only [Bw, List.map_cons, List.prod_cons]
        rfl
      rw [this]

      simp_rw [hBA A bA hbA (val ℓ), Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      rw [Matrix.mul_apply]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

  obtain ⟨bC, hbC⟩ := hb ℂ
  let V := ↥(parabolicHoms ℂ Γ ℂ)
  have hparC : ∀ (ℓ : ℕ) [NeZero ℓ] (v : V), heckeT M H ℓ ℂ (v : H1 M H ℂ) ∈ parabolicHoms ℂ Γ ℂ :=
    fun ℓ _ v => hTpar ℂ ℓ v v.2
  let TV : ∀ (ℓ : ℕ) [NeZero ℓ], Module.End ℂ V := fun ℓ _ =>
    (TL M H ℂ ℓ).restrict (p := parabolicHoms ℂ Γ ℂ) (q := parabolicHoms ℂ Γ ℂ) (fun v hv => hTpar ℂ ℓ v hv)
  have hTV : ∀ (ℓ : ℕ) [NeZero ℓ] (v : V), ((TV ℓ v : V) : H1 M H ℂ) = heckeT M H ℓ ℂ (v : H1 M H ℂ) :=
    fun ℓ _ v => rfl

  let τ := LinearMap.toMatrixAlgEquiv bC
  have hτ : ∀ (ℓ : ℕ) [NeZero ℓ] (T : Module.End ℂ V),
      (∀ v : V, ((T v : V) : H1 M H ℂ) = heckeT M H ℓ ℂ (v : H1 M H ℂ)) →
      τ T = (Bmat ℓ).map (Int.cast : ℤ → ℂ) := by
    intro ℓ _ T hT
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, Matrix.map_apply]
    have hTj : T (bC j) = ∑ k, ((Bmat ℓ k j : ℤ) : ℂ) • bC k := by
      apply Subtype.ext
      rw [hT, hBA ℂ bC hbC ℓ j, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul]
    have := bC.equivFun.apply_symm_apply (fun k => ((Bmat ℓ k j : ℤ) : ℂ))
    rw [Module.Basis.equivFun_symm_apply] at this
    have h2 := congrFun this i
    rw [Module.Basis.equivFun_apply] at h2
    rw [hTj]
    exact h2

  have hC := hC2aC (TV p) (hTV p)

  let castM : Matrix (Fin n₀) (Fin n₀) ℤ →+* Matrix (Fin n₀) (Fin n₀) ℂ := (Int.castRingHom ℂ).mapMatrix
  have hcastM : ∀ X : Matrix (Fin n₀) (Fin n₀) ℤ, castM X = X.map (Int.cast : ℤ → ℂ) := fun X => rfl
  set SZ : Set (Matrix (Fin n₀) (Fin n₀) ℤ) := Set.range (fun ℓ : I => @Bmat ℓ.1 (hval ℓ)) with hSZ
  have himg : τ (TV p) ∈ Submodule.span ℂ ((Submonoid.closure SZ).map castM.toMonoidHom : Set _) := by
    have h1 : τ (TV p) ∈ (Algebra.adjoin ℂ {T : Module.End ℂ V |
        ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ ¬ ℓ ∣ M ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          ((T v : V) : CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)}).map
          τ.toAlgHom := ⟨_, hC, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    have h2 : (τ.toAlgHom '' {T : Module.End ℂ V |
        ∃ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S ∧ ¬ ℓ ∣ M ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          ((T v : V) : CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)}) ⊆
        castM '' SZ := by
      rintro _ ⟨T, ⟨ℓ, hℓ, hℓS, hℓM, hT⟩, rfl⟩
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      refine ⟨Bmat ℓ, ⟨⟨ℓ, hℓ, hℓS, hℓM⟩, rfl⟩, ?_⟩
      rw [hcastM]
      exact (hτ ℓ T hT).symm
    have h3 := Algebra.adjoin_mono h2 h1
    rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at h3
    have h4 : (Submonoid.closure (castM '' SZ) : Set (Matrix (Fin n₀) (Fin n₀) ℂ)) =
        ((Submonoid.closure SZ).map castM.toMonoidHom : Set _) := by
      rw [MonoidHom.map_mclosure]; rfl
    rw [h4] at h3
    exact h3

  have himg' : (Bmat p).map (Int.cast : ℤ → ℂ) ∈ Submodule.span ℂ
      (Set.range fun m : ↥(Submonoid.closure SZ) => (m : Matrix (Fin n₀) (Fin n₀) ℤ).map (Int.cast : ℤ → ℂ)) := by
    rw [← hτ p (TV p) (hTV p)]
    convert himg using 2
    ext X
    simp only [Set.mem_range, Submonoid.coe_map, Set.mem_image, SetLike.mem_coe, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩
  obtain ⟨n, hn, s, z, hnz⟩ := exists_nsmul_eq_sum_of_mem_span_map _ _ himg'

  have hword : ∀ m : ↥(Submonoid.closure SZ), ∃ l : List I, Bw l = (m : Matrix (Fin n₀) (Fin n₀) ℤ) := by
    rintro ⟨m, hm⟩
    obtain ⟨L, hL, rfl⟩ := Submonoid.exists_list_of_mem_closure hm
    induction L with
    | nil => exact ⟨[], by simp [Bw]⟩
    | cons y L ih =>
      obtain ⟨l, hl⟩ := ih (fun y' hy' => hL y' (List.mem_cons_of_mem _ hy')) (Submonoid.list_prod_mem _
        (fun y' hy' => Submonoid.subset_closure (hL y' (List.mem_cons_of_mem _ hy'))))
      obtain ⟨ℓ, rfl⟩ := hL y (List.mem_cons_self)
      refine ⟨ℓ :: l, ?_⟩
      simp only [Bw, List.map_cons, List.prod_cons] at hl ⊢
      rw [hl]
  choose wl hwl using hword

  refine ⟨n, hn, ∑ m ∈ s, z m • ((wl m).map fun ℓ => MvPolynomial.X ℓ).prod, ?_⟩

  intro A _ _ _ φ hφ hφ0 a b ha hb0
  obtain ⟨bA, hbA⟩ := hb A

  have hops : ∀ j : Fin n₀, (n : A) • heckeT M H p A (bA j : H1 M H A) =
      ∑ m ∈ s, (z m : A) • TwL M H I val hval A (wl m) (bA j : H1 M H A) := by
    intro j
    rw [hBA A bA hbA p j, Finset.smul_sum]
    simp_rw [hBwA A bA hbA, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have hij := congrFun (congrFun hnz i) j
    simp only [Matrix.smul_apply, Matrix.sum_apply] at hij
    simp only [nsmul_eq_mul, smul_eq_mul] at hij
    have hijA := congrArg (Int.cast : ℤ → A) hij
    push_cast at hijA
    rw [hijA]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hwl m]

  have hφ' : φ ∈ parabolicHoms A Γ A := hφ
  set φV : ↥(parabolicHoms A Γ A) := ⟨φ, hφ'⟩ with hφV
  have hopsφ : (n : A) • heckeT M H p A φ = ∑ m ∈ s, (z m : A) • TwL M H I val hval A (wl m) φ := by
    let f₁ : ↥(parabolicHoms A Γ A) →ₗ[A] H1 M H A := ((n : A) • TL M H A p) ∘ₗ (parabolicHoms A Γ A).subtype
    let f₂ : ↥(parabolicHoms A Γ A) →ₗ[A] H1 M H A :=
      (∑ m ∈ s, (z m : A) • TwL M H I val hval A (wl m)) ∘ₗ (parabolicHoms A Γ A).subtype
    have hf : f₁ = f₂ := bA.ext fun j => by
      simp only [f₁, f₂, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply,
        LinearMap.coe_sum, Finset.sum_apply, TL_apply]
      exact hops j
    have := congrArg (fun f => f φV) hf
    simp only [f₁, f₂, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply,
      LinearMap.coe_sum, Finset.sum_apply, TL_apply, hφV] at this
    exact this

  rw [hb0] at hopsφ
  simp_rw [TwL_eigen M H I val hval A φ a ha, smul_smul] at hopsφ
  try rw [← Finset.sum_smul] at hopsφ
  try rw [smul_smul] at hopsφ

  have hscal : (n : A) * b = ∑ m ∈ s, (z m : A) * ((wl m).map a).prod := by
    by_contra hne
    apply hφ0
    have h := sub_eq_zero.mpr hopsφ
    rw [← sub_smul] at h
    ext γ
    have := congrArg (fun f : H1 M H A => f γ) h
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.zero_apply, smul_eq_mul, mul_eq_zero] at this
    rcases this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hne
    · simp at h0 ⊢
      exact h0
  rw [hscal, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_zsmul, zsmul_eq_mul, map_list_prod, List.map_map]
  congr 2
  refine List.map_congr_left fun ℓ _ => ?_
  simp

theorem solution
    (M : ℕ) [NeZero M] (S : Set ℕ) (hS : S.Finite)
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ∃ (n : ℕ) (_ : n ≠ 0) (P : MvPolynomial {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M} ℤ),
      ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A]
        (φ : CohCarrier.H1 M ⊤ A)
        (_ : φ ∈ ModularCurve.Period.parabolicHoms A (CohCarrier.GammaH M ⊤) A) (_ : φ ≠ 0)
        (a : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M} → A) (b : A),
        (∀ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M}, haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩;
          CohCarrier.heckeT M ⊤ ℓ.1 A φ = a ℓ • φ) →
        (haveI : NeZero p := ⟨hp.ne_zero⟩; CohCarrier.heckeT M ⊤ p A φ = b • φ) →
        (n : A) * b = MvPolynomial.aeval a P :=
  C2aSol.main M ⊤ S hS hp hpM
    (CohCarrier.mem_adjoin_heckeT_parabolicHoms_gammaH_top_of_finite M S hS hp hpM)

end S_CohCarrier_exists_mvPolynomial_heckeT_eigenvalue_of_mem_parabolicHoms_gammaH_top
end P2MW
export P2MW.S_CohCarrier_exists_mvPolynomial_heckeT_eigenvalue_of_mem_parabolicHoms_gammaH_top (solution)

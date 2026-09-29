-- Prove2me | solution 1 for CohCarrier.exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/daef34ba-f199-597f-bfd2-ed6f05a5b0f9

import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodHomPair
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_ModularCurve_periodMap_rescaleLin_apply
import Theorems.Thm_CohCarrier_exists_eichlerShimura_H1_top
import Theorems.Thm_ModularCurve_existsPeriodMapLinear
import Theorems.Thm_CuspForm_exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_CohCarrier_heckeT_mem_parabolicHoms
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X"
p2m_attr_erase "simp" "ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply"
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CongruenceSubgroup CohCarrier ModularCurve ModularCurve.Period

namespace OldAtP

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

theorem iDegL_ES_eq {M L d : ℕ} [NeZero M] [NeZero L] [NeZero d] (hd : LevelLE M L ⊤ ⊤ d)
    (hdR : d * M ∣ L)
    (ES : (CuspForm (Gamma0 M) 2 × CuspForm (Gamma0 M) 2) →ₗ[ℂ] H1 M ⊤ ℂ)
    (hES : ∀ (fg : CuspForm (Gamma0 M) 2 × CuspForm (Gamma0 M) 2) (γ : ↥(GammaH M ⊤)),
      ES fg (Additive.ofMul γ) = periodHomPair M fg (Additive.ofMul ⟨(γ : SL(2, ℤ)), GammaH_le_Gamma0 ⊤ γ.2⟩))
    (ES' : (CuspForm (Gamma0 L) 2 × CuspForm (Gamma0 L) 2) →ₗ[ℂ] H1 L ⊤ ℂ)
    (hES' : ∀ (fg : CuspForm (Gamma0 L) 2 × CuspForm (Gamma0 L) 2) (γ : ↥(GammaH L ⊤)),
      ES' fg (Additive.ofMul γ) = periodHomPair L fg (Additive.ofMul ⟨(γ : SL(2, ℤ)), GammaH_le_Gamma0 ⊤ γ.2⟩))
    (f g : CuspForm (Gamma0 M) 2) :
    iDegL M L ⊤ ⊤ d ℂ ℂ hd (ES (f, g)) =
      ES' (FreyPackage.ModMCarrier.rescaleLin hdR 2 f, FreyPackage.ModMCarrier.rescaleLin hdR 2 g) := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using Additive.rec with
  | ofMul γ' =>
  show ES (f, g) (Additive.ofMul (iotaDeg M L ⊤ ⊤ d hd γ')) = _
  rw [hES, hES', periodHomPair_apply_eq, periodHomPair_apply_eq,
    periodMap_rescaleLin_apply hdR hd f γ', periodMap_rescaleLin_apply hdR hd g γ']
  have hJ : ∀ (F : CuspForm (Gamma0 M) 2),
      periodMap L (FreyPackage.ModMCarrier.rescaleLin hdR 2 F)
        (Additive.ofMul (jConjGamma0 L ⟨(γ' : SL(2, ℤ)), GammaH_le_Gamma0 ⊤ γ'.2⟩)) =
      periodMap M F (Additive.ofMul (jConjGamma0 M ⟨(iotaDeg M L ⊤ ⊤ d hd γ' : SL(2, ℤ)),
        GammaH_le_Gamma0 ⊤ (iotaDeg M L ⊤ ⊤ d hd γ').2⟩)) := by
    intro F
    have e1 : jConjGamma0 L ⟨(γ' : SL(2, ℤ)), GammaH_le_Gamma0 ⊤ γ'.2⟩ =
        ⟨((⟨jConjSL (γ' : SL(2, ℤ)), jConjSL_mem_GammaH_top γ'⟩ : ↥(GammaH L ⊤)) : SL(2, ℤ)),
          GammaH_le_Gamma0 ⊤ (jConjSL_mem_GammaH_top γ')⟩ := Subtype.ext rfl
    have e2 : jConjGamma0 M ⟨(iotaDeg M L ⊤ ⊤ d hd γ' : SL(2, ℤ)),
        GammaH_le_Gamma0 ⊤ (iotaDeg M L ⊤ ⊤ d hd γ').2⟩ =
        ⟨(iotaDeg M L ⊤ ⊤ d hd ⟨jConjSL (γ' : SL(2, ℤ)), jConjSL_mem_GammaH_top γ'⟩ : SL(2, ℤ)),
          GammaH_le_Gamma0 ⊤ (iotaDeg M L ⊤ ⊤ d hd _).2⟩ := by
      apply Subtype.ext
      show jConjSL _ = _
      rw [iotaDeg_jConj]
    rw [e1, e2, periodMap_rescaleLin_apply hdR hd F]
  rw [hJ f, hJ g]

theorem complex
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : LevelLE M (M * p) ⊤ ⊤ 1) (hp : LevelLE M (M * p) ⊤ ⊤ p)
    (S : Finset ℕ) (a : ℕ → ℂ)
    (w : H1 (M * p) ⊤ ℂ) (hw : w ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH (M * p) ⊤) ℂ)
    (heig : ∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
      heckeT (M * p) ⊤ ℓ ℂ w = a ℓ • w)
    (hocc : ∃ w₀ : H1 M ⊤ ℂ, w₀ ≠ 0 ∧ w₀ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH M ⊤) ℂ ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p), heckeT M ⊤ ℓ ℂ w₀ = a ℓ • w₀) :
    ∃ y₁ y₂ : H1 M ⊤ ℂ,
      y₁ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH M ⊤) ℂ ∧
      y₂ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH M ⊤) ℂ ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
        heckeT M ⊤ ℓ ℂ y₁ = a ℓ • y₁ ∧ heckeT M ⊤ ℓ ℂ y₂ = a ℓ • y₂) ∧
      w = iDegL M (M * p) ⊤ ⊤ 1 ℂ ℂ h1 y₁ + iDegL M (M * p) ⊤ ⊤ p ℂ ℂ hp y₂ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ES, hESap, hESinj, hESrange, hEST, -⟩ := exists_eichlerShimura_H1_top M
  obtain ⟨ES', hES'ap, hES'inj, hES'range, hES'T, -⟩ := exists_eichlerShimura_H1_top (M * p)
  have h1R : 1 * M ∣ M * p := ⟨p, by ring⟩
  have hpR : p * M ∣ M * p := ⟨1, by ring⟩

  have heigen : ∀ (L : ℕ) [NeZero L]
      (E : (CuspForm (Gamma0 L) 2 × CuspForm (Gamma0 L) 2) →ₗ[ℂ] H1 L ⊤ ℂ)
      (_ : Function.Injective E)
      (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ L) (f g : CuspForm (Gamma0 L) 2),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        E (CuspForm.heckeTLin 2 hℓ hℓN f, CuspForm.heckeTLin 2 hℓ hℓN g) = heckeT L ⊤ ℓ ℂ (E (f, g)))
      (f g : CuspForm (Gamma0 L) 2) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ L) (c : ℂ),
      heckeT L ⊤ ℓ ℂ (E (f, g)) = c • E (f, g) →
      CuspForm.heckeTLin 2 hℓ hℓN f = c • f ∧ CuspForm.heckeTLin 2 hℓ hℓN g = c • g := by
    intro L _ E hEinj hET f g ℓ _ hℓ hℓN c hc
    have h := hET ℓ hℓ hℓN f g
    rw [hc, ← map_smul, Prod.smul_mk] at h
    have := hEinj h
    rw [Prod.mk.injEq] at this
    exact this

  have hw' : w ∈ LinearMap.range ES' := by rw [hES'range]; exact hw
  obtain ⟨⟨f, g⟩, rfl⟩ := hw'
  obtain ⟨w₀, hw₀ne, hw₀par, hw₀eig⟩ := hocc
  have hw₀' : w₀ ∈ LinearMap.range ES := by rw [hESrange]; exact hw₀par
  obtain ⟨⟨f₀, g₀⟩, rfl⟩ := hw₀'

  have hoccF : ∃ G : CuspForm (Gamma0 M) 2, G ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (_ : ¬ ℓ ∣ M * p), ℓ ∉ S →
        CuspForm.heckeTLin 2 hℓ hℓM G = a ℓ • G := by
    by_cases hf₀ : f₀ = 0
    · refine ⟨g₀, ?_, ?_⟩
      · rintro rfl; apply hw₀ne; rw [hf₀, Prod.mk_zero_zero, map_zero]
      · intro ℓ hℓ hℓM hℓMp hℓS
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        exact (heigen M ES hESinj hEST f₀ g₀ ℓ hℓ hℓM (a ℓ) (hw₀eig ℓ hℓ hℓS hℓMp)).2
    · refine ⟨f₀, hf₀, ?_⟩
      intro ℓ hℓ hℓM hℓMp hℓS
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact (heigen M ES hESinj hEST f₀ g₀ ℓ hℓ hℓM (a ℓ) (hw₀eig ℓ hℓ hℓS hℓMp)).1

  have hfg : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M * p), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN f = a ℓ • f ∧ CuspForm.heckeTLin 2 hℓ hℓN g = a ℓ • g := by
    intro ℓ hℓ hℓN hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact heigen (M * p) ES' hES'inj hES'T f g ℓ hℓ hℓN (a ℓ) (heig ℓ hℓ hℓS hℓN)
  obtain ⟨h₁, h₂, hh, hfeq⟩ :=
    CuspForm.exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level M p hpM h1R hpR S a f
      (fun ℓ hℓ hℓN hℓS => (hfg ℓ hℓ hℓN hℓS).1) hoccF
  obtain ⟨h₁', h₂', hh', hgeq⟩ :=
    CuspForm.exists_eq_rescaleLin_add_rescaleLin_of_heckeTLin_eq_smul_of_exists_level M p hpM h1R hpR S a g
      (fun ℓ hℓ hℓN hℓS => (hfg ℓ hℓ hℓN hℓS).2) hoccF
  refine ⟨ES (h₁, h₁'), ES (h₂, h₂'), ?_, ?_, ?_, ?_⟩
  · rw [← hESrange]; exact LinearMap.mem_range_self _ _
  · rw [← hESrange]; exact LinearMap.mem_range_self _ _
  · intro ℓ _ hℓ hℓS hℓN
    have hℓM : ¬ ℓ ∣ M := fun h => hℓN (h.mul_right p)
    constructor
    · rw [← hEST ℓ hℓ hℓM, (hh ℓ hℓ hℓM hℓN hℓS).1, (hh' ℓ hℓ hℓM hℓN hℓS).1, ← Prod.smul_mk, map_smul]
    · rw [← hEST ℓ hℓ hℓM, (hh ℓ hℓ hℓM hℓN hℓS).2, (hh' ℓ hℓ hℓM hℓN hℓS).2, ← Prod.smul_mk, map_smul]
  · rw [iDegL_ES_eq h1 h1R ES hESap ES' hES'ap, iDegL_ES_eq hp hpR ES hESap ES' hES'ap, ← map_add,
      Prod.mk_add_mk, ← hfeq, ← hgeq]

end OldAtP

namespace OldAtP

theorem Gamma_le_GammaH_top (L : ℕ) : Gamma L ≤ GammaH L ⊤ := by
  intro A hA
  rw [mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 L := by rw [Gamma0_mem]; exact hA'.2.2.1
  exact ⟨h0, Subgroup.mem_top _⟩

scoped instance GammaH_top_finiteIndex (L : ℕ) [NeZero L] : (GammaH L ⊤).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH_top L)

section Coeff

variable (L : ℕ) {A B : Type*} [AddCommGroup A] [AddCommGroup B]

open Subgroup Subgroup.leftTransversals in
theorem transfer_comp {G : Type*} [Group G] {K : Subgroup G} {C C' : Type*} [CommGroup C] [CommGroup C']
    [K.FiniteIndex] (ψ : C →* C') (ϕ : K →* C) :
    MonoidHom.transfer (ψ.comp ϕ) = ψ.comp (MonoidHom.transfer ϕ) := by
  ext g
  rw [MonoidHom.comp_apply, MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default]
  simp only [diff, map_prod, MonoidHom.comp_apply]

theorem heckeT_comp (Hs : Subgroup (ZMod L)ˣ) (ℓ : ℕ) [NeZero ℓ] (f : A →+ B) (φ : H1 L Hs A) :
    heckeT L Hs ℓ B (f.comp φ) = f.comp (heckeT L Hs ℓ A φ) := by
  have h1 : (AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp (conjL L Hs ℓ) =
      (AddMonoidHom.toMultiplicative f).comp
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL L Hs ℓ)) := by
    ext; rfl
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight (f.comp φ)).comp
      (conjL L Hs ℓ))) = f.comp (MonoidHom.toAdditiveLeft (MonoidHom.transfer
        ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL L Hs ℓ))))
  rw [h1, transfer_comp]
  ext; rfl

theorem comp_mem_parabolicHoms {R R' : Type*} [Semiring R] [Semiring R'] [Module R A] [Module R' B]
    (f : A →+ B) {φ : H1 L ⊤ A}
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms R (GammaH L ⊤) A) :
    f.comp φ ∈ ModularCurve.Period.parabolicHoms R' (GammaH L ⊤) B := by
  rw [mem_parabolicHoms_iff] at hφ ⊢
  intro γ hγ
  simp [hφ γ hγ]

theorem mem_parabolicHoms_int {R : Type*} [Semiring R] [Module R A] (φ : H1 L ⊤ A) :
    φ ∈ ModularCurve.Period.parabolicHoms R (GammaH L ⊤) A ↔
      φ ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH L ⊤) A := by
  rw [mem_parabolicHoms_iff, mem_parabolicHoms_iff]

theorem comp_sum {ι : Type*} (s : Finset ι) (f : A →+ B) (g : ι → H1 L ⊤ A) :
    f.comp (∑ i ∈ s, g i) = ∑ i ∈ s, f.comp (g i) :=
  map_sum (AddMonoidHom.compHom f) g s

end Coeff

section Algebraic

variable {F : Type} [Field F] [CharZero F]

theorem isAlgebraic_of_heckeT_eq_smul (L : ℕ) [NeZero L] (ℓ : ℕ) [NeZero ℓ] (c : F)
    (v : H1 L ⊤ F) (hv : v ∈ ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F) (hv0 : v ≠ 0)
    (h : heckeT L ⊤ ℓ F v = c • v) : IsAlgebraic ℚ c := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis_parabolicHoms_of_isAddTorsionFree (GammaH L ⊤)
  obtain ⟨bF, hbF⟩ := hb F
  haveI : Module.Free F (ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F) := Module.Free.of_basis bF
  haveI : Module.Finite F (ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F) := Module.Finite.of_basis bF
  have hstab : ∀ x ∈ ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F,
      heckeTL L ⊤ F ℓ x ∈ ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F := fun x hx => by
    rw [heckeTL_apply, mem_parabolicHoms_int] at *
    exact heckeT_mem_parabolicHoms L ⊤ F ℓ x hx
  set τ : Module.End F (ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F) :=
    (heckeTL L ⊤ F ℓ).restrict hstab with hτ
  have hstabZ : ∀ j, heckeT L ⊤ ℓ ℤ (b j : H1 L ⊤ ℤ) ∈ ModularCurve.Period.parabolicHoms ℤ (GammaH L ⊤) ℤ :=
    fun j => heckeT_mem_parabolicHoms L ⊤ ℤ ℓ _ (b j).2
  set A : Matrix (Fin n) (Fin n) ℤ := fun i j => b.repr ⟨_, hstabZ j⟩ i with hA
  have hcastb : ∀ i, (Int.castAddHom F).comp ((b i : ModularCurve.Period.parabolicHoms ℤ (GammaH L ⊤) ℤ) :
      H1 L ⊤ ℤ) = (bF i : H1 L ⊤ F) := fun i => (hbF i).symm
  have hTb : ∀ j, heckeT L ⊤ ℓ ℤ ((b j : ModularCurve.Period.parabolicHoms ℤ (GammaH L ⊤) ℤ) : H1 L ⊤ ℤ) =
      ∑ i, A i j • ((b i : ModularCurve.Period.parabolicHoms ℤ (GammaH L ⊤) ℤ) : H1 L ⊤ ℤ) := by
    intro j
    have := b.sum_repr ⟨_, hstabZ j⟩
    have h2 := congrArg (fun z : ModularCurve.Period.parabolicHoms ℤ (GammaH L ⊤) ℤ => (z : H1 L ⊤ ℤ)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hτb : ∀ j, τ (bF j) = ∑ i, (A i j : F) • bF i := by
    intro j
    apply Subtype.ext
    rw [Submodule.coe_sum, LinearMap.restrict_coe_apply, heckeTL_apply]
    simp only [Submodule.coe_smul]
    rw [← hcastb j, heckeT_comp, hTb, comp_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (Int.castAddHom F).comp (A i j • ((b i : ModularCurve.Period.parabolicHoms ℤ (GammaH L ⊤) ℤ) :
        H1 L ⊤ ℤ)) = A i j • (Int.castAddHom F).comp ((b i : ModularCurve.Period.parabolicHoms ℤ (GammaH L ⊤) ℤ) :
        H1 L ⊤ ℤ) := map_zsmul (AddMonoidHom.compHom (Int.castAddHom F)) _ _
    rw [e1, hcastb, Int.cast_smul_eq_zsmul]
  have hmat : LinearMap.toMatrix bF bF τ = A.map (Int.castRingHom F) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hτb, bF.repr_sum_self]
    rfl
  have hchar : τ.charpoly = A.charpoly.map (Int.castRingHom F) := by
    rw [← LinearMap.charpoly_toMatrix τ bF, hmat, Matrix.charpoly_map]

  set x : ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F := ⟨v, hv⟩ with hx
  have hx0 : x ≠ 0 := fun h0 => hv0 (congrArg Subtype.val h0)
  have hτx : τ x = c • x := by
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, heckeTL_apply, Submodule.coe_smul]
    exact h
  have hev : Module.End.HasEigenvector τ c x :=
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hτx, hx0⟩
  have h0 := Module.End.aeval_apply_of_hasEigenvector hev (p := τ.charpoly)
  rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at h0
  have heval : Polynomial.eval c τ.charpoly = 0 := by
    rcases smul_eq_zero.mp h0.symm with h | h
    · exact h
    · exact absurd h hx0
  rw [hchar, Polynomial.eval_map] at heval
  have hint : IsIntegral ℤ c := ⟨A.charpoly, Matrix.charpoly_monic A, by rwa [algebraMap_int_eq]⟩
  exact (hint.tower_top (A := ℚ)).isAlgebraic

end Algebraic

end OldAtP
p2m_reactivate "P2MW.S_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul.OldAtP"

namespace OldAtP

section OverE

variable {E : Type} [Field E] [CharZero E]

theorem overE (σ : E →+* ℂ)
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : LevelLE M (M * p) ⊤ ⊤ 1) (hp : LevelLE M (M * p) ⊤ ⊤ p)
    (S : Finset ℕ) (a : ℕ → E)
    (w : H1 (M * p) ⊤ E) (hw : w ∈ ModularCurve.Period.parabolicHoms E (GammaH (M * p) ⊤) E)
    (heig : ∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
      heckeT (M * p) ⊤ ℓ E w = a ℓ • w)
    (w₀ : H1 M ⊤ E) (hw₀ : w₀ ≠ 0) (hw₀par : w₀ ∈ ModularCurve.Period.parabolicHoms E (GammaH M ⊤) E)
    (hw₀eig : ∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
      heckeT M ⊤ ℓ E w₀ = a ℓ • w₀) :
    ∃ y₁ y₂ : H1 M ⊤ E,
      y₁ ∈ ModularCurve.Period.parabolicHoms E (GammaH M ⊤) E ∧
      y₂ ∈ ModularCurve.Period.parabolicHoms E (GammaH M ⊤) E ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
        heckeT M ⊤ ℓ E y₁ = a ℓ • y₁ ∧ heckeT M ⊤ ℓ E y₂ = a ℓ • y₂) ∧
      w = iDegL M (M * p) ⊤ ⊤ 1 E E h1 y₁ + iDegL M (M * p) ⊤ ⊤ p E E hp y₂ := by
  classical

  letI : Module E ℂ := Module.compHom ℂ σ
  have hsmul : ∀ (e : E) (z : ℂ), e • z = σ e * z := fun _ _ => rfl
  let σL : E →ₗ[E] ℂ :=
    { toFun := σ
      map_add' := σ.map_add
      map_smul' := fun e x => by rw [RingHom.id_apply, hsmul, smul_eq_mul, map_mul] }
  have hσL : ∀ e, σL e = σ e := fun _ => rfl
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective σL
    (LinearMap.ker_eq_bot.mpr (fun x y hxy => σ.injective hxy))
  have hρσ : ∀ e : E, ρ (σ e) = e := fun e => by
    have := LinearMap.congr_fun hρ e
    simpa [hσL] using this

  have hup : ∀ (L : ℕ) (ℓ : ℕ) [NeZero ℓ] (φ : H1 L ⊤ E) (c : E),
      heckeT L ⊤ ℓ E φ = c • φ → heckeT L ⊤ ℓ ℂ (σ.toAddMonoidHom.comp φ) = σ c • σ.toAddMonoidHom.comp φ := by
    intro L ℓ _ φ c hφ
    rw [heckeT_comp, hφ]
    ext γ
    simp
  have hdown : ∀ (L : ℕ) (ℓ : ℕ) [NeZero ℓ] (φ : H1 L ⊤ ℂ) (c : E),
      heckeT L ⊤ ℓ ℂ φ = σ c • φ → heckeT L ⊤ ℓ E (ρ.toAddMonoidHom.comp φ) = c • ρ.toAddMonoidHom.comp φ := by
    intro L ℓ _ φ c hφ
    rw [heckeT_comp, hφ]
    ext γ
    show ρ (σ c * φ _) = c * ρ (φ _)
    rw [← hsmul, map_smul, smul_eq_mul]

  have hσw₀ : σ.toAddMonoidHom.comp w₀ ≠ 0 := by
    intro h0
    apply hw₀
    refine AddMonoidHom.ext fun x => ?_
    have : σ (w₀ x) = 0 := DFunLike.congr_fun h0 x
    exact σ.injective (by rw [this, AddMonoidHom.zero_apply, map_zero])
  obtain ⟨z₁, z₂, hz₁, hz₂, hzeig, hzeq⟩ := complex M p hpM h1 hp S (fun ℓ => σ (a ℓ))
    (σ.toAddMonoidHom.comp w) (comp_mem_parabolicHoms _ _ hw)
    (fun ℓ _ hℓ hℓS hℓN => hup _ ℓ w (a ℓ) (heig ℓ hℓ hℓS hℓN))
    ⟨σ.toAddMonoidHom.comp w₀, hσw₀, comp_mem_parabolicHoms _ _ hw₀par,
      fun ℓ _ hℓ hℓS hℓN => hup _ ℓ w₀ (a ℓ) (hw₀eig ℓ hℓ hℓS hℓN)⟩
  refine ⟨ρ.toAddMonoidHom.comp z₁, ρ.toAddMonoidHom.comp z₂, comp_mem_parabolicHoms _ _ hz₁,
    comp_mem_parabolicHoms _ _ hz₂, ?_, ?_⟩
  · intro ℓ _ hℓ hℓS hℓN
    exact ⟨hdown _ ℓ z₁ (a ℓ) (hzeig ℓ hℓ hℓS hℓN).1, hdown _ ℓ z₂ (a ℓ) (hzeig ℓ hℓ hℓS hℓN).2⟩
  · have hwback : w = ρ.toAddMonoidHom.comp (σ.toAddMonoidHom.comp w) := by
      ext γ; simp [hρσ]
    rw [hwback, hzeq, AddMonoidHom.comp_add]
    rfl

end OverE
p2m_reactivate "P2MW.S_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul.OldAtP"

end OldAtP
p2m_reactivate "P2MW.S_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul.OldAtP"

namespace OldAtP

section Ascent

variable {F : Type} [Field F] [CharZero F]

theorem heckeT_smulF (L : ℕ) (ℓ : ℕ) [NeZero ℓ] (c : F) (φ : H1 L ⊤ F) :
    heckeT L ⊤ ℓ F (c • φ) = c • heckeT L ⊤ ℓ F φ :=
  (heckeTL L ⊤ F ℓ).map_smul c φ

theorem heckeT_sumF (L : ℕ) (ℓ : ℕ) [NeZero ℓ] {ι : Type*} (s : Finset ι) (g : ι → H1 L ⊤ F) :
    heckeT L ⊤ ℓ F (∑ i ∈ s, g i) = ∑ i ∈ s, heckeT L ⊤ ℓ F (g i) :=
  map_sum (heckeTL L ⊤ F ℓ) g s

variable (E : IntermediateField ℚ F)

theorem incl_comp_smul (L : ℕ) (e : E) (φ : H1 L ⊤ E) :
    (algebraMap E F).toAddMonoidHom.comp (e • φ) = (algebraMap E F e) • (algebraMap E F).toAddMonoidHom.comp φ := by
  ext γ
  simp

theorem eq_zero_of_sum_smul_comp_eq_zero (L : ℕ) {m : ℕ} (v : Fin m → F) (hv : LinearIndependent E v)
    (z : Fin m → H1 L ⊤ E)
    (h : ∑ k, v k • ((algebraMap E F).toAddMonoidHom.comp (z k)) = 0) : ∀ k, z k = 0 := by
  intro k
  refine AddMonoidHom.ext fun x => ?_
  have hx := DFunLike.congr_fun h x
  rw [AddMonoidHom.zero_apply, AddMonoidHom.finset_sum_apply] at hx
  have hx' : ∑ j, (z j x) • v j = 0 := by
    rw [← hx]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
    rfl
  have := Fintype.linearIndependent_iff.mp hv (fun j => z j x) hx' k
  simpa using this

theorem expand (L : ℕ) [NeZero L] (u : H1 L ⊤ F) (hu : u ∈ ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F) :
    ∃ (m : ℕ) (v : Fin m → F) (_ : LinearIndependent E v) (x : Fin m → H1 L ⊤ E),
      (∀ k, x k ∈ ModularCurve.Period.parabolicHoms E (GammaH L ⊤) E) ∧
      u = ∑ k, v k • (algebraMap E F).toAddMonoidHom.comp (x k) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis_parabolicHoms_of_isAddTorsionFree (GammaH L ⊤)
  obtain ⟨bF, hbF⟩ := hb F
  obtain ⟨bE, hbE⟩ := hb E
  have hcast : ∀ i, (algebraMap E F).toAddMonoidHom.comp ((bE i : ModularCurve.Period.parabolicHoms E (GammaH L ⊤) E) :
      H1 L ⊤ E) = (bF i : H1 L ⊤ F) := by
    intro i
    rw [hbE i, hbF i]
    ext γ
    simp

  set c : Fin n → F := fun i => bF.repr ⟨u, hu⟩ i with hc
  set V : Submodule E F := Submodule.span E (Set.range c) with hV
  haveI : Module.Finite E V := Module.Finite.span_of_finite E (Set.finite_range c)
  set vb := Module.finBasis E V with hvb
  set m := Module.finrank E V
  have hcmem : ∀ i, c i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  set e : Fin n → Fin m → E := fun i k => vb.repr ⟨c i, hcmem i⟩ k with he
  refine ⟨m, fun k => (vb k : F), vb.linearIndependent.map' V.subtype (Submodule.ker_subtype V),
    fun k => ∑ i, e i k • ((bE i : ModularCurve.Period.parabolicHoms E (GammaH L ⊤) E) : H1 L ⊤ E), ?_, ?_⟩
  · intro k
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bE i).2
  ·
    have hu' : u = ∑ i, c i • (bF i : H1 L ⊤ F) := by
      have := congrArg (fun z : ModularCurve.Period.parabolicHoms F (GammaH L ⊤) F => (z : H1 L ⊤ F))
        (bF.sum_repr ⟨u, hu⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm

    have hci : ∀ i, c i = ∑ k, (e i k) • ((vb k : V) : F) := by
      intro i
      have := congrArg (fun z : V => (z : F)) (vb.sum_repr ⟨c i, hcmem i⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hu']
    simp_rw [comp_sum, incl_comp_smul, hcast, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, hci]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [IntermediateField.smul_def, smul_eq_mul, mul_comm]
    rfl

theorem eigen_of_expand (L : ℕ) (ℓ : ℕ) [NeZero ℓ] {m : ℕ} (v : Fin m → F) (hv : LinearIndependent E v)
    (x : Fin m → H1 L ⊤ E) (cE : E)
    (h : heckeT L ⊤ ℓ F (∑ k, v k • (algebraMap E F).toAddMonoidHom.comp (x k)) =
      algebraMap E F cE • ∑ k, v k • (algebraMap E F).toAddMonoidHom.comp (x k)) :
    ∀ k, heckeT L ⊤ ℓ E (x k) = cE • x k := by
  have key := eq_zero_of_sum_smul_comp_eq_zero E L v hv (fun k => heckeT L ⊤ ℓ E (x k) - cE • x k) (by
    have e1 : ∀ k, v k • (algebraMap E F).toAddMonoidHom.comp (heckeT L ⊤ ℓ E (x k) - cE • x k) =
        heckeT L ⊤ ℓ F (v k • (algebraMap E F).toAddMonoidHom.comp (x k)) -
          algebraMap E F cE • (v k • (algebraMap E F).toAddMonoidHom.comp (x k)) := by
      intro k
      rw [AddMonoidHom.comp_sub, smul_sub, ← heckeT_comp, heckeT_smulF, incl_comp_smul, smul_comm]
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, ← heckeT_sumF, ← Finset.smul_sum, h, sub_self])
  intro k
  exact sub_eq_zero.mp (key k)

end Ascent
p2m_reactivate "P2MW.S_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul.OldAtP"

end OldAtP
p2m_reactivate "P2MW.S_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul.OldAtP"

open OldAtP in
theorem solution
    {F : Type} [Field F] [CharZero F]
    (M p : ℕ) [NeZero M] [Fact p.Prime] [NeZero (M * p)] (hpM : ¬ p ∣ M)
    (h1 : LevelLE M (M * p) ⊤ ⊤ 1) (hp : LevelLE M (M * p) ⊤ ⊤ p)
    (S : Finset ℕ) (a : ℕ → F)
    (w : H1 (M * p) ⊤ F) (hw : w ∈ ModularCurve.Period.parabolicHoms F (GammaH (M * p) ⊤) F)
    (heig : ∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
      heckeT (M * p) ⊤ ℓ F w = a ℓ • w)
    (hocc : ∃ w₀ : H1 M ⊤ F, w₀ ≠ 0 ∧ w₀ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p), heckeT M ⊤ ℓ F w₀ = a ℓ • w₀) :
    ∃ y₁ y₂ : H1 M ⊤ F,
      y₁ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F ∧
      y₂ ∈ ModularCurve.Period.parabolicHoms F (GammaH M ⊤) F ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
        heckeT M ⊤ ℓ F y₁ = a ℓ • y₁ ∧ heckeT M ⊤ ℓ F y₂ = a ℓ • y₂) ∧
      w = iDegL M (M * p) ⊤ ⊤ 1 F F h1 y₁ + iDegL M (M * p) ⊤ ⊤ p F F hp y₂ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨w₀, hw₀ne, hw₀par, hw₀eig⟩ := hocc

  set E : IntermediateField ℚ F := algebraicClosure ℚ F with hE
  haveI : Algebra.IsAlgebraic ℚ E := algebraicClosure.isAlgebraic ℚ F
  have σ : E →ₐ[ℚ] ℂ := IsAlgClosed.lift

  have halg : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M * p → a ℓ ∈ E := by
    intro ℓ _ hℓ hℓS hℓN
    rw [hE, mem_algebraicClosure_iff]
    exact isAlgebraic_of_heckeT_eq_smul M ℓ (a ℓ) w₀ hw₀par hw₀ne (hw₀eig ℓ hℓ hℓS hℓN)
  let aE : ℕ → E := fun ℓ =>
    if h : ∃ _ : NeZero ℓ, ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M * p then
      ⟨a ℓ, by obtain ⟨_, h1', h2', h3'⟩ := h; exact halg ℓ h1' h2' h3'⟩ else 0
  have haE : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M * p → algebraMap E F (aE ℓ) = a ℓ := by
    intro ℓ _ hℓ hℓS hℓN
    have hh : ∃ _ : NeZero ℓ, ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ M * p := ⟨inferInstance, hℓ, hℓS, hℓN⟩
    simp only [aE, dif_pos hh]
    rfl

  obtain ⟨m, v, hv, x, hxpar, hwx⟩ := expand E (M * p) w hw
  obtain ⟨m₀, v₀, hv₀, x₀, hx₀par, hw₀x⟩ := expand E M w₀ hw₀par
  have hxeig : ∀ (k : Fin m) (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M * p →
      heckeT (M * p) ⊤ ℓ E (x k) = aE ℓ • x k := by
    intro k ℓ _ hℓ hℓS hℓN
    refine eigen_of_expand E (M * p) ℓ v hv x (aE ℓ) ?_ k
    rw [← hwx, haE ℓ hℓ hℓS hℓN]
    exact heig ℓ hℓ hℓS hℓN
  have hx₀eig : ∀ (k : Fin m₀) (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M * p →
      heckeT M ⊤ ℓ E (x₀ k) = aE ℓ • x₀ k := by
    intro k ℓ _ hℓ hℓS hℓN
    refine eigen_of_expand E M ℓ v₀ hv₀ x₀ (aE ℓ) ?_ k
    rw [← hw₀x, haE ℓ hℓ hℓS hℓN]
    exact hw₀eig ℓ hℓ hℓS hℓN

  obtain ⟨k₀, hk₀⟩ : ∃ k₀, x₀ k₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hw₀ne
    rw [hw₀x]
    exact Finset.sum_eq_zero fun k _ => by rw [hall k, AddMonoidHom.comp_zero, smul_zero]

  have hdec : ∀ k, ∃ y₁ y₂ : H1 M ⊤ E,
      y₁ ∈ ModularCurve.Period.parabolicHoms E (GammaH M ⊤) E ∧
      y₂ ∈ ModularCurve.Period.parabolicHoms E (GammaH M ⊤) E ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (_ : ℓ.Prime) (_ : ℓ ∉ S) (_ : ¬ ℓ ∣ M * p),
        heckeT M ⊤ ℓ E y₁ = aE ℓ • y₁ ∧ heckeT M ⊤ ℓ E y₂ = aE ℓ • y₂) ∧
      x k = iDegL M (M * p) ⊤ ⊤ 1 E E h1 y₁ + iDegL M (M * p) ⊤ ⊤ p E E hp y₂ := fun k =>
    overE (σ : E →+* ℂ) M p hpM h1 hp S aE (x k) (hxpar k) (fun ℓ _ hℓ hℓS hℓN => hxeig k ℓ hℓ hℓS hℓN)
      (x₀ k₀) hk₀ (hx₀par k₀) (fun ℓ _ hℓ hℓS hℓN => hx₀eig k₀ ℓ hℓ hℓS hℓN)
  choose y₁ y₂ hy₁ hy₂ hyeig hyeq using hdec
  refine ⟨∑ k, v k • (algebraMap E F).toAddMonoidHom.comp (y₁ k),
    ∑ k, v k • (algebraMap E F).toAddMonoidHom.comp (y₂ k), ?_, ?_, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (comp_mem_parabolicHoms _ _ (hy₁ k))
  · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (comp_mem_parabolicHoms _ _ (hy₂ k))
  · intro ℓ _ hℓ hℓS hℓN
    constructor
    · rw [heckeT_sumF, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [heckeT_smulF, heckeT_comp, (hyeig k ℓ hℓ hℓS hℓN).1, incl_comp_smul, haE ℓ hℓ hℓS hℓN, smul_comm]
    · rw [heckeT_sumF, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [heckeT_smulF, heckeT_comp, (hyeig k ℓ hℓ hℓS hℓN).2, incl_comp_smul, haE ℓ hℓ hℓS hℓN, smul_comm]
  · rw [hwx, map_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hyeq k, AddMonoidHom.comp_add, smul_add, LinearMap.map_smul, LinearMap.map_smul]
    rfl

end S_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul
end P2MW
export P2MW.S_CohCarrier_exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul (solution)

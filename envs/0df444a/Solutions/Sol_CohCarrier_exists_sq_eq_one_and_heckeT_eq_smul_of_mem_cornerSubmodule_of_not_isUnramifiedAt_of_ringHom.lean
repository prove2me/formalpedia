-- Prove2me | solution 1 for CohCarrier.exists_sq_eq_one_and_heckeT_eq_smul_of_mem_cornerSubmodule_of_not_isUnramifiedAt_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1593804e-b63b-521c-a981-aac614ef0d55

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_CuspForm_heckeLocal_exists_algEquiv_cornerRing_H1_of_not_isEisenstein
import Theorems.Thm_CuspForm_heckeLocal_pi_U_sq_eq_one_of_not_sq_dvd_of_not_isUnramifiedAt
import Theorems.Thm_ResidualGaloisRep_exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible
import Theorems.Thm_IsLocalRing_sq_eq_one_iff_of_isUnit_two
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_GaloisRep_Residual
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_sq_eq_one_and_heckeT_eq_smul_of_mem_cornerSubmodule_of_not_isUnramifiedAt_of_ringHom
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 TateModule.instModule TateModule.instSMul AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow HeckeEis.instFiniteProjLineCusps ModularCurve.numberField_of_finiteDimensional Deep.NTSupply.instNormalRayClassSubgroup"
p2m_attr_erase "instance" "NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe"
p2m_attr_erase "simp" "ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec HeckeEis.coeffCoboundaryMap_apply PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.tateMap_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk HeckeEis.coe_linePow ModularCurve.symPoly_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Polynomial IsLocalRing
open scoped IsMulCommutative

namespace EPSSol

theorem trace_eq_neg_coeff_one {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (h2 : Module.finrank k V = 2) (f : Module.End k V) :
    LinearMap.trace k V f = -(LinearMap.charpoly f).coeff 1 := by
  classical
  let b := Module.finBasisOfFinrankEq k V h2
  rw [LinearMap.trace_eq_matrix_trace k b, ← LinearMap.charpoly_toMatrix f b,
    Matrix.trace_eq_neg_charpoly_coeff]
  simp

end EPSSol

set_option maxHeartbeats 16000000 in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) (hram : ¬ ρbar.IsUnramifiedAt q)
    (L : ℕ) [NeZero L] (hqL : q ∣ L) (hqL2 : ¬ q ^ 2 ∣ L)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime ∧ ¬ r ∣ L)
    (hcomm : ∀ g h : CohCarrier.Gen L (↑S : Set ℕ),
      CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g * CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 h =
        CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 h * CohCarrier.opFamily L ⊤ (↑S : Set ℕ) 𝒪 g)
    (θbar : CohCarrier.Gen L (↑S : Set ℕ) → ResidueField 𝒪)
    (hθbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓL : ¬ ℓ ∣ L),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓL)) * X + C (ℓ : ResidueField 𝒪))

    (θ : CuspForm.heckeAlgebra L 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ L),
      θbar (CohCarrier.Gen.T ℓ hℓ hℓS hℓN) = θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    (hθU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ L),
      θbar (CohCarrier.Gen.U q hq hqN) =
        θ (CuspForm.heckeAlgebra.U hq hqN (fun h => (hS q h).2 hqN)))

    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata L ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra)
    (i₀ : Fin Sp.n) (πk : Sp.CornerRing i₀ →ₐ[𝒪] ResidueField 𝒪)
    (hπk : ∀ g : CohCarrier.Gen L (↑S : Set ℕ), πk (Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata L ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op g,
        Algebra.subset_adjoin (Set.mem_range_self g)⟩) = θbar g)
    (hpar : ∀ v : CohCarrier.H1 L ⊤ 𝒪,
      v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
        v ∈ ModularCurve.Period.parabolicHoms 𝒪 (CohCarrier.GammaH L ⊤) 𝒪) :
    ∃ ε : 𝒪, ε ^ 2 = 1 ∧
      ∀ v : CohCarrier.H1 L ⊤ 𝒪,
        v ∈ IharaLemma.cornerSubmodule (M := CohCarrier.H1 L ⊤ 𝒪) (Sp.e i₀) →
          (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeT L ⊤ q 𝒪 v) = ε • v := by
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact (CuspForm.HasIntegralStructure L 2) := ⟨CuspForm.hasIntegralStructure_two L⟩
  have hS' : ∀ r : ℕ, r.Prime → r ∣ L → r ∉ (↑S : Set ℕ) := fun r _ hrL h => (hS r h).2 hrL

  have hpk : (p : ResidueField 𝒪) = 0 := by
    rw [← map_natCast (IsLocalRing.residue 𝒪), IsLocalRing.residue_eq_zero_iff]
    exact hp𝒪
  haveI : CharP (ResidueField 𝒪) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpk

  have hEis : ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓN : ¬ ℓ ∣ L), ℓ ≡ 1 [MOD L] ∧
      θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) ≠ (ℓ : ResidueField 𝒪) + 1 := by
    obtain ⟨ℓ, A, σ, hℓ, hℓS, hℓL, hmod, hA, hσ, htr⟩ :=
      ResidualGaloisRep.exists_prime_modEq_one_isFrobeniusAt_trace_ne_add_one_of_isAbsolutelyIrreducible
        p hp2 ρbar habs L S
    have hℓS' : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS (Finset.mem_coe.mp h)
    refine ⟨ℓ, hℓ, hℓS', hℓL, hmod, ?_⟩
    rw [← hθT ℓ hℓ hℓS' hℓL]
    have hcp := hθbar ℓ hℓ hℓS' hℓL A hA σ hσ
    have htr' : LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) = θbar (CohCarrier.Gen.T ℓ hℓ hℓS' hℓL) := by
      rw [EPSSol.trace_eq_neg_coeff_one ρbar.finrank_eq, hcp]
      simp [coeff_one]
    rwa [htr'] at htr

  obtain ⟨e, heT, heU⟩ := CuspForm.heckeLocal.exists_algEquiv_cornerRing_H1_of_not_isEisenstein
    L (↑S : Set ℕ) hS' 𝒪 θ hcomm θbar hθT hθU Sp i₀ πk hπk hEis

  set Sbig : Finset ℕ := S ∪ L.primeFactors ∪ {p} with hSbig
  have hS₀S : S ⊆ Sbig := Finset.subset_union_left.trans Finset.subset_union_left
  have hSbigP : ∀ r ∈ Sbig, r.Prime := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · rcases Finset.mem_union.mp hr with hr | hr
      · exact (hS r hr).1
      · exact Nat.prime_of_mem_primeFactors hr
    · rw [Finset.mem_singleton] at hr; rw [hr]; exact Fact.out
  have hpS : p ∈ Sbig := Finset.mem_union_right _ (Finset.mem_singleton_self p)
  have hLS : ∀ r : ℕ, r.Prime → r ∣ L → r ∈ Sbig := fun r hr hrL =>
    Finset.mem_union_left _ (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hr, hrL, NeZero.ne L⟩))
  have hθ' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ L) (hℓS : ℓ ∉ (↑Sbig : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓN
              (fun h => hℓS (Finset.coe_subset.mpr hS₀S h)))) * X + C (ℓ : ResidueField 𝒪) := by
    intro ℓ hℓ hℓN hℓS P hP σ hσ
    have hℓS0 : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS (Finset.coe_subset.mpr hS₀S h)
    rw [hθbar ℓ hℓ hℓS0 hℓN P hP σ hσ, hθT ℓ hℓ hℓS0 hℓN]
  have hsq := CuspForm.heckeLocal.pi_U_sq_eq_one_of_not_sq_dvd_of_not_isUnramifiedAt
    p hp𝒪 ρbar habs Sbig S hS₀S hSbigP hpS L hLS hS' θ hθ' q hq hqp hqL hqL2 hram

  haveI : IsLocalRing (CuspForm.heckeLocal L (↑S : Set ℕ) 𝒪 θ) := CuspForm.heckeLocal.isLocalRing L (↑S : Set ℕ) 𝒪 θ
  have h2𝒪 : IsUnit (2 : 𝒪) := by
    by_contra h2n
    have h2m : (2 : 𝒪) ∈ maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal _).mpr h2n
    have hcop : IsCoprime (2 : 𝒪) (p : 𝒪) := by
      have h := (Nat.isCoprime_iff_coprime.mpr
        ((Nat.coprime_primes Nat.prime_two Fact.out).mpr (Ne.symm hp2))).map (Int.castRingHom 𝒪)
      simpa using h
    obtain ⟨a, b, hab⟩ := hcop
    have h1 : (1 : 𝒪) ∈ maximalIdeal 𝒪 := by
      rw [← hab]
      exact add_mem (Ideal.mul_mem_left _ _ h2m) (Ideal.mul_mem_left _ _ hp𝒪)
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have h2 : IsUnit (2 : CuspForm.heckeLocal L (↑S : Set ℕ) 𝒪 θ) := by
    have h := h2𝒪.map (algebraMap 𝒪 (CuspForm.heckeLocal L (↑S : Set ℕ) 𝒪 θ))
    rwa [map_ofNat] at h
  obtain ⟨ε, hε1, hεU⟩ : ∃ ε : 𝒪, ε ^ 2 = 1 ∧
      CuspForm.heckeLocal.π L (↑S : Set ℕ) 𝒪 θ (CuspForm.heckeAlgebra.U hq hqL (hS' q hq hqL)) =
        algebraMap 𝒪 _ ε := by
    rcases (IsLocalRing.sq_eq_one_iff_of_isUnit_two h2 _).mp hsq with h | h
    · exact ⟨1, one_pow 2, by rw [h, map_one]⟩
    · exact ⟨-1, by norm_num, by rw [h, map_neg, map_one]⟩
  refine ⟨ε, hε1, fun v hv => ?_⟩

  have hcorner : Sp.toCornerRing i₀
      ⟨(CohCarrier.hdata L ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.U q hq hqL),
        Algebra.subset_adjoin (Set.mem_range_self _)⟩ = algebraMap 𝒪 (Sp.CornerRing i₀) ε := by
    rw [← heU q hq hqL, hεU, AlgEquiv.commutes]

  let B := ↥(CohCarrier.hdata L ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).opSubalgebra
  obtain ⟨t, ht⟩ : ∃ t : B, t =
    ⟨(CohCarrier.hdata L ⊤ (↑S : Set ℕ) 𝒪 (ResidueField 𝒪) hcomm θbar).op (CohCarrier.Gen.U q hq hqL),
      Algebra.subset_adjoin (Set.mem_range_self _)⟩ := ⟨_, rfl⟩
  rw [← ht] at hcorner

  have hev : ((Sp.e i₀ : B) : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v = v := by
    obtain ⟨v0, hv0⟩ := hv
    rw [← hv0]
    show ((Sp.e i₀ : B) * (Sp.e i₀ : B) : B) • v0 = (Sp.e i₀ : B) • v0
    rw [(Sp.idem i₀).eq]

  have hcB := congrArg (fun z : Sp.CornerRing i₀ => ((z : B) : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v) hcorner
  simp only [IharaLemma.IdempotentSplitting.coe_toCornerRing,
    IharaLemma.IdempotentSplitting.algebraMap_base_cornerRing_coe] at hcB

  have hte : (t : B) * (Sp.e i₀ : B) = (Sp.e i₀ : B) * t := mul_comm _ _
  rw [mul_assoc, hte, ← mul_assoc, (Sp.idem i₀).eq] at hcB

  have lhs : (((Sp.e i₀ : B) * t : B) : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v =
      ((t : B) : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v := by
    rw [← hte, Subalgebra.coe_mul, Module.End.mul_apply, hev]
  have rhs : (((Sp.e i₀ : B) * algebraMap 𝒪 B ε * (Sp.e i₀ : B) : B) : Module.End 𝒪 (CohCarrier.H1 L ⊤ 𝒪)) v =
      ε • v := by
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Module.End.mul_apply, Module.End.mul_apply, hev,
      Subalgebra.coe_algebraMap, Module.algebraMap_end_apply, map_smul, hev]
  rw [lhs, rhs, ht] at hcB
  exact hcB

end S_CohCarrier_exists_sq_eq_one_and_heckeT_eq_smul_of_mem_cornerSubmodule_of_not_isUnramifiedAt_of_ringHom
end P2MW
export P2MW.S_CohCarrier_exists_sq_eq_one_and_heckeT_eq_smul_of_mem_cornerSubmodule_of_not_isUnramifiedAt_of_ringHom (solution)

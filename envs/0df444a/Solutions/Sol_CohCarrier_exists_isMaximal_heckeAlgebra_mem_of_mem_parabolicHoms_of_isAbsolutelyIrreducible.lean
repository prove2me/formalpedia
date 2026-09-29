-- Prove2me | solution 1 for CohCarrier.exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/71a9e49b-eaa4-5804-be89-2cef1832b4bd

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_coeff_comp_smul_eq_zero
import Theorems.Thm_CohCarrier_jDeg_heckeT_comm_flat
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm
import Theorems.Thm_CohCarrier_exists_gamma0_lift_dvd
import Theorems.Thm_CohCarrier_transfer_restrict_eq_pow_index
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Theorems.Thm_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
import Theorems.Thm_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
import Theorems.Thm_TW12CD1Dock_subsingleton_H2_gamma0
import Theorems.Thm_CohCarrier_exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fintype.Parity
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Schreier

import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.KrullTopology
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"
set_option autoImplicit false

section PieceZ

open scoped MatrixGroups
open CongruenceSubgroup

private theorem diamondRaw_comp_coeff (M : ℕ) (H : Subgroup (ZMod M)ˣ) {A B : Type} [AddCommGroup A]
    [AddCommGroup B] (g : A →+ B) (σ : Gamma0 M) (φ : CohCarrier.H1 M H A) :
    CohCarrier.diamondRaw M H B σ (g.comp φ) = g.comp (CohCarrier.diamondRaw M H A σ φ) :=
  rfl

private theorem comp_mem_parabolicHoms {M : ℕ} {H : Subgroup (ZMod M)ˣ} {A B : Type} [AddCommGroup A]
    [AddCommGroup B] {R R' : Type} [Semiring R] [Semiring R'] [Module R A] [Module R' B] (g : A →+ B)
    (φ : CohCarrier.H1 M H A) (hφ : φ ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) A) :
    g.comp φ ∈ ModularCurve.Period.parabolicHoms R' (CohCarrier.GammaH M H) B := by
  intro γ hγ
  show g (φ (Additive.ofMul γ)) = 0
  rw [hφ γ hγ, map_zero]

private theorem comp_zsmul_H1 {M : ℕ} {H : Subgroup (ZMod M)ˣ} {A B : Type} [AddCommGroup A]
    [AddCommGroup B] (g : A →+ B) (z : ℤ) (φ : CohCarrier.H1 M H A) : g.comp (z • φ) = z • g.comp φ := by
  ext γ
  show g (z • φ γ) = z • g (φ γ)
  exact map_zsmul g z (φ γ)

private theorem exists_eq_smul_of_castAddHom_comp_eq_zero (p : ℕ) [NeZero p] {M : ℕ}
    {H : Subgroup (ZMod M)ˣ} (φ : CohCarrier.H1 M H ℤ) (h : (Int.castAddHom (ZMod p)).comp φ = 0) :
    ∃ ψ : CohCarrier.H1 M H ℤ, φ = (p : ℤ) • ψ := by
  have hdvd : ∀ γ, (p : ℤ) ∣ φ γ := fun γ =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (DFunLike.congr_fun h γ)
  refine ⟨{ toFun := fun γ => φ γ / p,
             map_zero' := by rw [map_zero, Int.zero_ediv],
             map_add' := fun γ δ => by rw [map_add, Int.add_ediv_of_dvd_left (hdvd γ)] }, ?_⟩
  ext γ
  show φ γ = (p : ℤ) • (φ γ / p)
  rw [smul_eq_mul, Int.mul_ediv_cancel' (hdvd γ)]

private theorem castAddHom_comp_ne_zero (p : ℕ) [NeZero p] {N : ℕ} {H : Subgroup (ZMod N)ˣ}
    (φ₀ : CohCarrier.H1 N H ℤ) (hφ₀ : ¬ ∃ ψ : CohCarrier.H1 N H ℤ, φ₀ = (p : ℤ) • ψ) :
    (Int.castAddHom (ZMod p)).comp φ₀ ≠ 0 :=
  fun h => hφ₀ (exists_eq_smul_of_castAddHom_comp_eq_zero p φ₀ h)

private theorem castAddHom_comp_smul_eq_zero (p : ℕ) {N : ℕ} {H : Subgroup (ZMod N)ˣ}
    (ψ : CohCarrier.H1 N H ℤ) : (Int.castAddHom (ZMod p)).comp ((p : ℤ) • ψ) = 0 :=
  CohCarrier.coeff_comp_smul_eq_zero N H (Int.castAddHom (ZMod p)) (p : ℤ)
    (fun a => by simp) ψ

private theorem diamondRaw_castAddHom_comp (p : ℕ) {N : ℕ} {H : Subgroup (ZMod N)ˣ}
    (φ₀ : CohCarrier.H1 N H ℤ)
    (hdia : ∀ σ : Gamma0 N, ∃ ψ : CohCarrier.H1 N H ℤ,
      CohCarrier.diamondRaw N H ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ)
    (σ : Gamma0 N) :
    CohCarrier.diamondRaw N H (ZMod p) σ ((Int.castAddHom (ZMod p)).comp φ₀)
      = (Int.castAddHom (ZMod p)).comp φ₀ := by
  obtain ⟨ψ, hψ⟩ := hdia σ
  rw [diamondRaw_comp_coeff, eq_add_of_sub_eq' hψ, AddMonoidHom.comp_add, castAddHom_comp_smul_eq_zero,
    add_zero]

private theorem heckeT_castAddHom_comp (p : ℕ) {N : ℕ} {H : Subgroup (ZMod N)ˣ} (S : Finset ℕ)
    (n : ℕ → ℤ) (φ₀ : CohCarrier.H1 N H ℤ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ ψ : CohCarrier.H1 N H ℤ, CohCarrier.heckeT N H ℓ ℤ φ₀ - n ℓ • φ₀ = (p : ℤ) • ψ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    CohCarrier.heckeT N H ℓ (ZMod p) ((Int.castAddHom (ZMod p)).comp φ₀)
      = n ℓ • (Int.castAddHom (ZMod p)).comp φ₀ := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨ψ, hψ⟩ := hT ℓ hℓ hℓS hℓN
  rw [CohCarrier.heckeT_comp_coeff, eq_add_of_sub_eq' hψ, AddMonoidHom.comp_add,
    castAddHom_comp_smul_eq_zero, add_zero, comp_zsmul_H1]

private theorem heckeT_castAddHom_comp' (p : ℕ) {N : ℕ} {H : Subgroup (ZMod N)ˣ} (S : Finset ℕ)
    (n : ℕ → ℤ) (φ₀ : CohCarrier.H1 N H ℤ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ ψ : CohCarrier.H1 N H ℤ, CohCarrier.heckeT N H ℓ ℤ φ₀ - n ℓ • φ₀ = (p : ℤ) • ψ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    CohCarrier.heckeT N H ℓ (ZMod p) ((Int.castAddHom (ZMod p)).comp φ₀)
      = (n ℓ : ZMod p) • (Int.castAddHom (ZMod p)).comp φ₀ := by
  rw [heckeT_castAddHom_comp p S n φ₀ hT ℓ hℓ hℓS hℓN]
  ext γ
  show n ℓ • ((Int.castAddHom (ZMod p)).comp φ₀) γ = ((n ℓ : ℤ) : ZMod p) • ((Int.castAddHom (ZMod p)).comp φ₀) γ
  rw [zsmul_eq_mul, smul_eq_mul]

private theorem castAddHom_comp_mem_parabolicHoms (p : ℕ) {N : ℕ} {H : Subgroup (ZMod N)ˣ}
    (φ₀ : CohCarrier.H1 N H ℤ)
    (hφ₀par : φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) ℤ) :
    (Int.castAddHom (ZMod p)).comp φ₀
      ∈ ModularCurve.Period.parabolicHoms (ZMod p) (CohCarrier.GammaH N H) (ZMod p) :=
  comp_mem_parabolicHoms (Int.castAddHom (ZMod p)) φ₀ hφ₀par

private theorem castAddHom_comp_apply_eq_zero_of_isOfFinOrder (p : ℕ) {N : ℕ} {H : Subgroup (ZMod N)ˣ}
    (φ₀ : CohCarrier.H1 N H ℤ) (γ : ↥(CohCarrier.GammaH N H)) (hγ : IsOfFinOrder γ) :
    ((Int.castAddHom (ZMod p)).comp φ₀) (Additive.ofMul γ) = 0 := by
  obtain ⟨m, hm, hγm⟩ := hγ.exists_pow_eq_one
  have h : m • φ₀ (Additive.ofMul γ) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, hγm, ofMul_one, map_zero]
  rw [AddMonoidHom.comp_apply, (smul_eq_zero.mp h).resolve_left hm.ne', map_zero]

private theorem not_exists_eq_smul_and_congr_of_castAddHom_comp_eq (p : ℕ) [NeZero p] {N : ℕ}
    {H : Subgroup (ZMod N)ˣ} (S : Finset ℕ) (n : ℕ → ℤ) (φ : CohCarrier.H1 N H ℤ)
    (w : CohCarrier.H1 N H (ZMod p)) (hφw : (Int.castAddHom (ZMod p)).comp φ = w) (hw : w ≠ 0)
    (hwT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N H ℓ (ZMod p) w = n ℓ • w) :
    (¬ ∃ ψ : CohCarrier.H1 N H ℤ, φ = (p : ℤ) • ψ) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ∃ ψ : CohCarrier.H1 N H ℤ, CohCarrier.heckeT N H ℓ ℤ φ - n ℓ • φ = (p : ℤ) • ψ := by
  refine ⟨?_, fun ℓ hℓ hℓS hℓN => ?_⟩
  · rintro ⟨ψ, rfl⟩
    exact hw (by rw [← hφw, castAddHom_comp_smul_eq_zero])
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    apply exists_eq_smul_of_castAddHom_comp_eq_zero p
    rw [AddMonoidHom.comp_sub, ← CohCarrier.heckeT_comp_coeff, comp_zsmul_H1, hφw, hwT ℓ hℓ hℓS hℓN,
      sub_self]

end PieceZ

section PieceWitness

open Polynomial

namespace PlaneRepresentation

section RingIdentities

variable {R : Type*} [Ring R]

private theorem mul_mul_eq_zero_of_sq_eq_zero {n m : R} (hn : n * n = 0) (hm : m * m = 0)
    (hu : (n + m + n * m) * (n + m + n * m) = 0) :
    n * (m * n) = 0 ∧ m * (n * m) = 0 ∧ n * m + m * n = 0 := by
  have hn' : ∀ r : R, n * (n * r) = 0 := fun r => by rw [← mul_assoc, hn, zero_mul]
  have hm' : ∀ r : R, m * (m * r) = 0 := fun r => by rw [← mul_assoc, hm, zero_mul]
  have star : n * m + m * n + m * (n * m) + n * (m * n) + n * (m * (n * m)) = 0 := by
    have e : (n + m + n * m) * (n + m + n * m) =
        n * n + n * m + n * (n * m) + m * n + m * m + m * (n * m) + n * (m * n) + n * (m * m) +
          n * (m * (n * m)) := by noncomm_ring
    rw [e, hn, hm, hn'] at hu
    simpa only [mul_zero, zero_add, add_zero] using hu
  have h1 : n * (m * n) + n * (m * (n * m)) = 0 := by
    have := congrArg (fun r => n * r) star
    simpa only [mul_add, hn', mul_zero, zero_add, add_zero] using this
  have h1m : n * (m * (n * m)) = 0 := by
    have := congrArg (fun r => r * m) h1
    simpa only [add_mul, zero_mul, mul_assoc, hm, mul_zero, zero_add, add_zero] using this
  have hnmn : n * (m * n) = 0 := by rw [h1m, add_zero] at h1; exact h1
  have h2 : m * (n * m) + n * (m * (n * m)) = 0 := by
    have := congrArg (fun r => r * m) star
    simpa only [add_mul, zero_mul, mul_assoc, hm, mul_zero, zero_add, add_zero, hn'] using this
  have hmnm : m * (n * m) = 0 := by rw [h1m, add_zero] at h2; exact h2
  refine ⟨hnmn, hmnm, ?_⟩
  simpa only [h1m, hmnm, hnmn, mul_zero, add_zero] using star

end RingIdentities

section Matrices

variable {k : Type} [Field k]

private theorem mul_eq_zero_of_sq_eq_zero {n m : Matrix (Fin 2) (Fin 2) k} (hn : n * n = 0)
    (hm : m * m = 0) (hu : (n + m + n * m) * (n + m + n * m) = 0) : n * m = 0 := by
  obtain ⟨hnmn, hmnm, hs⟩ := mul_mul_eq_zero_of_sq_eq_zero hn hm hu
  have E : ∀ X : Matrix (Fin 2) (Fin 2) k, X = 0 → ∀ i j, X i j = 0 := fun X hX i j => by
    rw [hX]; rfl
  have hn00 := E _ hn 0 0; have hn01 := E _ hn 0 1; have hn10 := E _ hn 1 0; have hn11 := E _ hn 1 1
  have hm00 := E _ hm 0 0; have hm01 := E _ hm 0 1; have hm10 := E _ hm 1 0; have hm11 := E _ hm 1 1
  have hnmn00 := E _ hnmn 0 0; have hnmn01 := E _ hnmn 0 1; have hnmn10 := E _ hnmn 1 0
  have hmnm00 := E _ hmnm 0 0
  have hs00 := E _ hs 0 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue] at hn00 hn01 hn10 hn11 hm00 hm01 hm10 hm11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue] at hnmn00 hnmn01 hnmn10 hmnm00
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue] at hs00
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, ← mul_self_eq_zero]
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (2*(m 1 1)^2) * hn00 + (-(m 1 1)*(m 1 0)) * hn01 + (2*(n 0 0)^2) * hm00 + ((n 0 0)*(n 1 0)) * hm01 + (2*(n 0 0)*(n 0 1)) * hm10 + (-2*(n 0 0)^2) * hm11 + (-2*(m 1 1)) * hnmn00 + ((m 1 0)) * hnmn01 + (-(n 0 0)) * hmnm00 + ((n 0 0)*(m 1 1)) * hs00
  · linear_combination ((m 0 1)^2) * hn00 + (2*(n 0 0)*(n 0 1)) * hm01 + ((n 0 1)^2) * hm11 + (-(n 0 1)*(m 0 1)) * hs00
  · linear_combination (2*(m 0 0)*(m 1 0)) * hn10 + ((m 1 0)^2) * hn11 + ((n 1 0)^2) * hm00 + (-(n 1 0)*(m 1 0)) * hs00
  · linear_combination ((m 1 1)^2) * hn00 + ((m 1 1)*(m 0 1)) * hn10 + ((m 1 1)^2) * hn11 + ((n 0 0)^2) * hm00 + ((n 0 0)*(n 0 1)) * hm10 + (-(n 0 0)^2) * hm11 + (-2*(m 1 1)) * hnmn00 + ((m 0 1)) * hnmn10 + (-(n 0 0)) * hmnm00 + ((n 0 0)*(m 1 1)) * hs00

private theorem exists_not_commute : ∃ X Y : Matrix (Fin 2) (Fin 2) k, X * Y ≠ Y * X := by
  refine ⟨Matrix.single 0 1 1, Matrix.single 1 0 1, fun h => ?_⟩
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h
  have := congrFun (congrFun h 0) 0
  simp at this

private theorem false_of_span_eq_top_matrix {G : Type*} [Group G] (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) (G₂ : Subgroup G) [hN : G₂.Normal]
    (hcomm : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ G₂) (huni : ∀ σ ∈ G₂, (ρ σ - 1) * (ρ σ - 1) = 0) : False := by

  have hall : ∀ P : Submodule k (Matrix (Fin 2) (Fin 2) k), Set.range ⇑ρ ⊆ P →
      ∀ X : Matrix (Fin 2) (Fin 2) k, X ∈ P := fun P hP X =>
    Submodule.span_le.mpr hP (hspan ▸ Submodule.mem_top)

  have hprod : ∀ σ ∈ G₂, ∀ τ ∈ G₂, (ρ σ - 1) * (ρ τ - 1) = 0 := fun σ hσ τ hτ =>
    mul_eq_zero_of_sq_eq_zero (huni σ hσ) (huni τ hτ) (by
      have h := huni (σ * τ) (G₂.mul_mem hσ hτ)
      rw [map_mul] at h
      convert h using 2 <;> noncomm_ring)
  by_cases hex : ∃ σ ∈ G₂, ρ σ - 1 ≠ 0
  swap
  ·
    have htriv : ∀ σ ∈ G₂, ρ σ - 1 = 0 := fun σ hσ => by_contra fun h => hex ⟨σ, hσ, h⟩
    have hcomm' : ∀ g h : G, ρ g * ρ h = ρ h * ρ g := fun g h => by
      have e : g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by group
      have hc : ρ (g * h * g⁻¹ * h⁻¹) = 1 := sub_eq_zero.mp (htriv _ (hcomm g h))
      have := congrArg ρ e
      rw [map_mul, map_mul, hc, one_mul, map_mul] at this
      exact this
    have h1 : ∀ X : Matrix (Fin 2) (Fin 2) k, ∀ g : G, ρ g * X = X * ρ g := fun X g => by
      have hX := hall (Subalgebra.toSubmodule (Subalgebra.centralizer k (Set.range ⇑ρ)))
        (by
          rintro _ ⟨h, rfl⟩
          rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
          rintro _ ⟨g, rfl⟩
          exact hcomm' g h) X
      rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hX
      exact hX _ ⟨g, rfl⟩
    have h2 : ∀ X Y : Matrix (Fin 2) (Fin 2) k, X * Y = Y * X := fun X Y => by
      have hY := hall (Subalgebra.toSubmodule (Subalgebra.center k (Matrix (Fin 2) (Fin 2) k)))
        (by
          rintro _ ⟨g, rfl⟩
          rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff]
          exact fun X => (h1 X g).symm) Y
      rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_center_iff] at hY
      exact hY X
    obtain ⟨X, Y, hXY⟩ := (exists_not_commute (k := k))
    exact hXY (h2 X Y)
  ·
    obtain ⟨σ₀, hσ₀, hn₀⟩ := hex
    set n₀ := ρ σ₀ - 1 with hn₀def
    have hconj : ∀ g : G, n₀ * (ρ g * n₀) = 0 := fun g => by
      have h := hprod σ₀ hσ₀ (g * σ₀ * g⁻¹) (hN.conj_mem σ₀ hσ₀ g)
      have hg : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      have hg' : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e : ρ (g * σ₀ * g⁻¹) - 1 = ρ g * n₀ * ρ g⁻¹ := by
        rw [hn₀def, map_mul, map_mul, mul_sub, sub_mul, mul_one, hg']
      rw [e] at h
      have h' := congrArg (fun X => X * ρ g) h
      simp only [zero_mul, mul_assoc, hg, mul_one] at h'
      exact h'
    have hX : ∀ X : Matrix (Fin 2) (Fin 2) k, n₀ * (X * n₀) = 0 := fun X =>
      hall (LinearMap.ker ((LinearMap.mulLeft k n₀).comp (LinearMap.mulRight k n₀)))
        (by
          rintro _ ⟨g, rfl⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulRight_apply,
            LinearMap.mulLeft_apply]
          exact hconj g) X
    have hentry : ∃ i j, n₀ i j ≠ 0 := by
      by_contra hc
      exact hn₀ (Matrix.ext fun i j => by_contra fun h => hc ⟨i, j, h⟩)
    obtain ⟨i, j, hij⟩ := hentry
    have h := congrFun (congrFun (hX (Matrix.single j i 1)) i) j
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single_apply] at h <;>
      simp_all

end Matrices

section Core

variable {k : Type} [Field k]

private theorem false_of_span_eq_top_of_forall_mem_unipotent {G : Type*} [Group G] {V : Type} [AddCommGroup V]
    [Module k V] (hV : Module.finrank k V = 2) (ρ : G →* Module.End k V)
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) (G₂ : Subgroup G) [G₂.Normal]
    (hcomm : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ G₂) (huni : ∀ σ ∈ G₂, (ρ σ - 1) * (ρ σ - 1) = 0) : False := by
  haveI : Module.Finite k V := Module.finite_of_finrank_pos (by rw [hV]; exact two_pos)
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hV
  let e : Module.End k V ≃ₐ[k] Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrixAlgEquiv b
  let ρM : G →* Matrix (Fin 2) (Fin 2) k := e.toMulEquiv.toMonoidHom.comp ρ
  refine false_of_span_eq_top_matrix ρM ?_ G₂ hcomm fun σ hσ => ?_
  · have hrange : Set.range ⇑ρM = ⇑e.toLinearEquiv.toLinearMap '' Set.range ⇑ρ := by
      rw [← Set.range_comp]; rfl
    rw [hrange, ← Submodule.map_span e.toLinearEquiv.toLinearMap, hspan, Submodule.map_top,
      LinearMap.range_eq_top]
    exact e.toLinearEquiv.surjective
  · have h := congrArg e (huni σ hσ)
    first | (simp only [map_mul, map_sub, map_one, map_zero] at h; exact h) | simpa only [map_mul, map_sub, map_one, map_zero] using h | simpa only [map_mul, map_sub, map_one, map_zero, ρM] using h

end Core

end PlaneRepresentation

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "baseChange IsAbsolutelyIrreducible factorsThroughFiniteLevel finrank_eq V ρ mk isAbsolutelyIrreducible_iff_span_eq_top"
p2m_open "ResidualGaloisRep"

section Generic

variable {k : Type} [Field k]

section Plane

variable {V : Type} [AddCommGroup V] [Module k V]

private theorem sub_one_mul_sub_one_eq_zero_of_trace_eq_two_of_det_eq_one (hV : Module.finrank k V = 2) (f : Module.End k V)
    (htr : LinearMap.trace k V f = 2) (hdet : LinearMap.det f = 1) : (f - 1) * (f - 1) = 0 := by
  haveI : Module.Finite k V := Module.finite_of_finrank_eq_succ hV
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hV
  apply (LinearMap.toMatrix b b).injective
  rw [LinearMap.toMatrix_mul b, map_sub, LinearMap.toMatrix_one b, map_zero]
  rw [LinearMap.trace_eq_matrix_trace k b] at htr
  rw [← LinearMap.det_toMatrix b] at hdet
  set A := LinearMap.toMatrix b b f with hA
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · linear_combination (A 0 0) * htr - hdet
  · linear_combination (A 0 1) * htr
  · linear_combination (A 1 0) * htr
  · linear_combination (A 1 1) * htr - hdet

private theorem trace_pow_eq_two_of_sub_one_mul_sub_one_eq_zero (hV : Module.finrank k V = 2) (f : Module.End k V)
    (hf : (f - 1) * (f - 1) = 0) (n : ℕ) : LinearMap.trace k V (f ^ n) = 2 := by
  haveI : Module.Finite k V := Module.finite_of_finrank_eq_succ hV
  set m : Module.End k V := f - 1 with hm
  have hfm : f = 1 + m := by rw [hm, add_sub_cancel]
  have hmm : m * m = 0 := hf
  have hpow : ∀ j : ℕ, f ^ j = 1 + (j : ℕ) • m := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih, hfm, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hmm, smul_zero, add_zero,
        add_assoc, succ_nsmul, add_comm m (j • m)]
  have htr1 : LinearMap.trace k V 1 = 2 := by
    rw [LinearMap.trace_one, hV]
    norm_num
  have htrm : LinearMap.trace k V m = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent ⟨2, by rw [pow_two]; exact hmm⟩).eq_zero
  rw [hpow n, map_add, htr1, map_nsmul, htrm, nsmul_zero, add_zero]

end Plane

private theorem _root_.ResidualGaloisRep.false_of_span_eq_top_of_forall_mem_unipotent {G : Type*} [Group G] {V : Type} [AddCommGroup V]
    [Module k V] (hV : Module.finrank k V = 2) (ρ : G →* Module.End k V)
    (hspan : Submodule.span k (Set.range ⇑ρ) = ⊤) (G₂ : Subgroup G) [G₂.Normal]
    (hcomm : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ G₂) (huni : ∀ σ ∈ G₂, (ρ σ - 1) * (ρ σ - 1) = 0) : False :=
  PlaneRepresentation.false_of_span_eq_top_of_forall_mem_unipotent hV ρ hspan G₂ hcomm huni

p2m_export "ResidualGaloisRep" "false_of_span_eq_top_of_forall_mem_unipotent"

private noncomputable def fixingDetOne (ρbar : ResidualGaloisRep k) (ζ : AlgebraicClosure ℚ) :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
  (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ) ⊓
    ((LinearMap.det : Module.End k ρbar.V →* k).comp ρbar.ρ).ker

private theorem mem_fixingDetOne_iff (ρbar : ResidualGaloisRep k) (ζ : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ∈ fixingDetOne ρbar ζ ↔ σ ζ = ζ ∧ LinearMap.det (ρbar.ρ σ) = 1 := by
  simp only [fixingDetOne, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker,
    MonoidHom.coe_comp, Function.comp_apply]
  rfl

private theorem fixingDetOne_normal (ρbar : ResidualGaloisRep k) {m : ℕ} [NeZero m] {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ m) : (fixingDetOne ρbar ζ).Normal := by
  refine ⟨fun σ hσ g => ?_⟩
  rw [mem_fixingDetOne_iff] at hσ ⊢
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := g⁻¹ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    have hσi : σ (g⁻¹ ζ) = g⁻¹ ζ := by rw [← hi, map_pow, hσ.1]
    have h := congrArg g hσi
    simpa [AlgEquiv.mul_apply] using h
  · rw [ρbar.ρ.map_mul, ρbar.ρ.map_mul, map_mul, map_mul, hσ.2, mul_one, ← map_mul, ← ρbar.ρ.map_mul,
      mul_inv_cancel, ρbar.ρ.map_one, map_one]

private theorem commutator_mem_fixingDetOne (ρbar : ResidualGaloisRep k) {m : ℕ} [NeZero m] {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ m) (g h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    g * h * g⁻¹ * h⁻¹ ∈ fixingDetOne ρbar ζ := by
  rw [mem_fixingDetOne_iff]
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := g⁻¹ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one (ξ := h⁻¹ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    have hg : g⁻¹ ζ = ζ ^ i := hi.symm
    have hh : h⁻¹ ζ = ζ ^ j := hj.symm

    have hcomm : g⁻¹ (h⁻¹ ζ) = h⁻¹ (g⁻¹ ζ) := by
      rw [hh, hg, map_pow, map_pow, hg, hh, ← pow_mul, ← pow_mul, mul_comm]
    have h1 : (g * h * g⁻¹ * h⁻¹) ζ = g (h (g⁻¹ (h⁻¹ ζ))) := by simp [AlgEquiv.mul_apply]
    rw [h1, hcomm]
    simp
  · set D : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* k :=
      (LinearMap.det : Module.End k ρbar.V →* k).comp ρbar.ρ with hD
    have hgg : D g * D g⁻¹ = 1 := by rw [← D.map_mul, mul_inv_cancel, D.map_one]
    have hhh : D h * D h⁻¹ = 1 := by rw [← D.map_mul, mul_inv_cancel, D.map_one]
    show D (g * h * g⁻¹ * h⁻¹) = 1
    rw [D.map_mul, D.map_mul, D.map_mul, mul_assoc (D g * D h), mul_mul_mul_comm, hgg, hhh, mul_one]

private theorem exists_apply_eq_and_det_eq_one_and_trace_ne_two (ρbar : ResidualGaloisRep k)
    (hirr : ρbar.IsAbsolutelyIrreducible) {m : ℕ} [NeZero m] {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ m) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ζ = ζ ∧ LinearMap.det (ρbar.ρ σ) = 1 ∧ LinearMap.trace k ρbar.V (ρbar.ρ σ) ≠ 2 := by
  by_contra hcon
  push Not at hcon
  haveI := fixingDetOne_normal ρbar hζ
  refine false_of_span_eq_top_of_forall_mem_unipotent ρbar.finrank_eq ρbar.ρ
    ((isAbsolutelyIrreducible_iff_span_eq_top ρbar).mp hirr) (fixingDetOne ρbar ζ)
    (commutator_mem_fixingDetOne ρbar hζ) fun σ hσ => ?_
  obtain ⟨hσζ, hσdet⟩ := (mem_fixingDetOne_iff ρbar ζ σ).mp hσ
  exact sub_one_mul_sub_one_eq_zero_of_trace_eq_two_of_det_eq_one ρbar.finrank_eq _ (hcon σ hσζ hσdet) hσdet

private theorem trace_apply_mul_mul_inv (ρbar : ResidualGaloisRep k) (g τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.trace k ρbar.V (ρbar.ρ (g * τ * g⁻¹)) = LinearMap.trace k ρbar.V (ρbar.ρ τ) := by
  rw [ρbar.ρ.map_mul, ρbar.ρ.map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← ρbar.ρ.map_mul, inv_mul_cancel,
    ρbar.ρ.map_one, one_mul]

private theorem pow_apply_eq_self {ζ : AlgebraicClosure ℚ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ζ = ζ)
    (j : ℕ) : (σ ^ j) ζ = ζ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hσ, ih]

private theorem modEq_one_of_isFrobeniusAt_of_apply_eq {m : ℕ} [NeZero m] {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ m) (A : ValuationSubring (AlgebraicClosure ℚ)) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hA : A.LiesOverPrime ℓ) (hτ : A.IsFrobeniusAt τ ℓ)
    (hm : m.Coprime ℓ) (hfix : τ ζ = ζ) : ℓ ≡ 1 [MOD m] := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  have hℓζ : ζ ^ ℓ = ζ :=
    (ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ ℓ m hA hτ hm ζ hζ.pow_eq_one).symm.trans hfix
  have hsub : ζ ^ (ℓ - 1) * ζ = 1 * ζ := by
    rw [← pow_succ, Nat.sub_add_cancel hℓ, hℓζ, one_mul]
  have hdvd : m ∣ ℓ - 1 := (hζ.pow_eq_one_iff_dvd _).mp (mul_right_cancel₀ hζ0 hsub)
  exact ((Nat.modEq_iff_dvd' hℓ).mpr hdvd).symm

private theorem exists_prime_notMem_not_dvd_modEq_one_trace_frobenius_ne_two_of_modulus (ρbar : ResidualGaloisRep k)
    (hirr : ρbar.IsAbsolutelyIrreducible) (m : ℕ) [NeZero m] (S : Finset ℕ) :
    ∃ ℓ₀ : ℕ, ℓ₀.Prime ∧ ℓ₀ ∉ S ∧ ¬ ℓ₀ ∣ m ∧ ℓ₀ ≡ 1 [MOD m] ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        A.LiesOverPrime ℓ₀ ∧ A.IsFrobeniusAt τ ℓ₀ ∧ LinearMap.trace k ρbar.V (ρbar.ρ τ) ≠ 2 := by
  classical

  obtain ⟨ζ, hζroot⟩ := IsAlgClosed.exists_root (cyclotomic m (AlgebraicClosure ℚ))
    (degree_cyclotomic_pos m _ (Nat.pos_of_ne_zero (NeZero.ne m))).ne'
  have hζ : IsPrimitiveRoot ζ m := (isRoot_cyclotomic_iff).mp hζroot

  obtain ⟨σ, hσζ, hσdet, hσtr⟩ := exists_apply_eq_and_det_eq_one_and_trace_ne_two ρbar hirr hζ

  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI : FiniteDimensional ℚ L := hLfd
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ} : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.adjoin.finiteDimensional
      ⟨X ^ m - C (1 : ℚ), monic_X_pow_sub_C 1 (NeZero.ne m), by simp [hζ.pow_eq_one]⟩
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_sup L _
  have hFopen : IsOpen (F.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    IntermediateField.fixingSubgroup_isOpen F
  have hLF : L ≤ F := le_sup_left
  have hζF : ζ ∈ F := (le_sup_right : IntermediateField.adjoin ℚ {ζ} ≤ F) (IntermediateField.subset_adjoin ℚ {ζ} rfl)
  have hρfix : ∀ u ∈ F.fixingSubgroup, ρbar.ρ u = 1 := fun u hu =>
    hL u fun x hx => (IntermediateField.mem_fixingSubgroup_iff F u).mp hu x (hLF hx)
  have hζfix : ∀ u ∈ F.fixingSubgroup, u ζ = ζ := fun u hu =>
    (IntermediateField.mem_fixingSubgroup_iff F u).mp hu ζ hζF

  let M : ℕ := m * (S.erase 0).prod id
  have hM : 0 < M := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne m))
    (Finset.prod_pos fun s hs => Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hs))

  obtain ⟨ℓ₀, A, τ, g, n, j, hℓ₀, hℓ₀M, hA, hτ, hmem₁, hmem₂⟩ :=
    Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen F.fixingSubgroup hFopen σ hM
  have hm_dvd_M : m ∣ M := dvd_mul_right m _
  have hℓ₀m : ¬ ℓ₀ ∣ m := fun h => hℓ₀M (h.trans hm_dvd_M)
  have hℓ₀S : ℓ₀ ∉ S := fun hS => hℓ₀M (dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem id (Finset.mem_erase.mpr ⟨hℓ₀.ne_zero, hS⟩)) m)

  have hconj₂ : g * τ * g⁻¹ = (g * τ * g⁻¹ * (σ ^ j)⁻¹) * σ ^ j := by group
  have hconj₁ : g * τ ^ n * g⁻¹ = (g * τ ^ n * g⁻¹ * σ⁻¹) * σ := by group
  have hB : ρbar.ρ (g * τ * g⁻¹) = ρbar.ρ σ ^ j := by
    rw [hconj₂, ρbar.ρ.map_mul, hρfix _ hmem₂, one_mul, ρbar.ρ.map_pow]
  have hσB : ρbar.ρ σ = ρbar.ρ (g * τ * g⁻¹) ^ n := by
    have h1 : ρbar.ρ σ = ρbar.ρ (g * τ ^ n * g⁻¹) := by
      rw [hconj₁, ρbar.ρ.map_mul, hρfix _ hmem₁, one_mul]
    rw [h1, ← ρbar.ρ.map_pow, conj_pow]
  refine ⟨ℓ₀, hℓ₀, hℓ₀S, hℓ₀m, ?_, A, τ, hA, hτ, ?_⟩
  ·
    have hcop : m.Coprime ℓ₀ := (Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hℓ₀).mpr hℓ₀m)
    have hζ' : IsPrimitiveRoot (g⁻¹ ζ) m := hζ.map_of_injective g⁻¹.injective
    have hgτ : (g * τ * g⁻¹) ζ = ζ := by
      rw [hconj₂, AlgEquiv.mul_apply, pow_apply_eq_self σ hσζ j]
      exact hζfix _ hmem₂
    have hfix : τ (g⁻¹ ζ) = g⁻¹ ζ := by
      apply g.injective
      simpa [AlgEquiv.mul_apply] using hgτ
    exact modEq_one_of_isFrobeniusAt_of_apply_eq hζ' A hℓ₀.one_le τ hA hτ hcop hfix
  ·
    rw [← trace_apply_mul_mul_inv ρbar g τ]
    intro htr2
    have hdetB : LinearMap.det (ρbar.ρ (g * τ * g⁻¹)) = 1 := by
      rw [hB, map_pow, hσdet, one_pow]
    have huni := sub_one_mul_sub_one_eq_zero_of_trace_eq_two_of_det_eq_one ρbar.finrank_eq _ htr2 hdetB
    exact hσtr (by rw [hσB]; exact trace_pow_eq_two_of_sub_one_mul_sub_one_eq_zero ρbar.finrank_eq _ huni n)

end Generic

private theorem exists_prime_notMem_not_dvd_modEq_one_trace_frobenius_ne_two
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ) [NeZero N] (S : Finset ℕ)
    (k : Type) [Field k] [CharP k p] (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) :
    ∃ ℓ₀ : ℕ, ℓ₀.Prime ∧ ℓ₀ ∉ S ∧ ¬ ℓ₀ ∣ N ∧ ℓ₀ ≡ 1 [MOD p] ∧ (∀ t : ℕ, t * t ∣ N → ℓ₀ ≡ 1 [MOD t]) ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        A.LiesOverPrime ℓ₀ ∧ A.IsFrobeniusAt σ ℓ₀ ∧ LinearMap.trace k ρbar.V (ρbar.ρ σ) ≠ 2 := by
  have _ := hp2
  haveI : NeZero (p * N) := ⟨mul_ne_zero (Fact.out : p.Prime).ne_zero (NeZero.ne N)⟩
  obtain ⟨ℓ₀, hℓ₀, hS, hdvd, hmod, hrest⟩ :=
    exists_prime_notMem_not_dvd_modEq_one_trace_frobenius_ne_two_of_modulus ρbar hirr (p * N) S
  refine ⟨ℓ₀, hℓ₀, hS, fun h => hdvd (h.trans (dvd_mul_left N p)), Nat.ModEq.of_mul_right N hmod,
    fun t ht => Nat.ModEq.of_dvd ((dvd_mul_left t t).trans (ht.trans (dvd_mul_left N p))) hmod, hrest⟩

private theorem exists_prime_notMem_not_dvd_modEq_one_not_dvd_sub_succ
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ) [NeZero N] (S : Finset ℕ) (n : ℕ → ℤ)
    (k : Type) [Field k] [CharP k p] (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (htr : ∀ (ℓ : ℕ) (_ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k)) :
    ∃ ℓ₀ : ℕ, ℓ₀.Prime ∧ ℓ₀ ∉ S ∧ ¬ ℓ₀ ∣ N ∧ (∀ t : ℕ, t * t ∣ N → ℓ₀ ≡ 1 [MOD t]) ∧
      ¬ (p : ℤ) ∣ n ℓ₀ - (ℓ₀ + 1 : ℕ) := by
  obtain ⟨ℓ₀, hℓ₀, hS, hN, hmodp, hsq, A, σ, hA, hσ, hne⟩ :=
    exists_prime_notMem_not_dvd_modEq_one_trace_frobenius_ne_two p hp2 N S k ρbar hirr
  refine ⟨ℓ₀, hℓ₀, hS, hN, hsq, fun hdvd => hne ?_⟩
  have hℓk : ((ℓ₀ : ℕ) : k) = 1 := by
    have h1 : ((ℓ₀ : ℕ) : k) = ((1 : ℕ) : k) := (CharP.natCast_eq_natCast k p).mpr hmodp
    rw [h1, Nat.cast_one]
  have hz : (((n ℓ₀ - (ℓ₀ + 1 : ℕ) : ℤ)) : k) = 0 := (CharP.intCast_eq_zero_iff k p _).mpr hdvd
  rw [htr ℓ₀ hℓ₀ hS hN A hA σ hσ]
  push_cast at hz
  rw [hℓk] at hz
  linear_combination hz

private theorem exists_prime_notMem_not_dvd_modEq_one_trace_frobenius_ne_succ
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ) [NeZero N] (S : Finset ℕ)
    (k : Type) [Field k] [CharP k p] (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible) :
    ∃ ℓ₀ : ℕ, ℓ₀.Prime ∧ ℓ₀ ∉ S ∧ ¬ ℓ₀ ∣ N ∧ (∀ t : ℕ, t * t ∣ N → ℓ₀ ≡ 1 [MOD t]) ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        A.LiesOverPrime ℓ₀ ∧ A.IsFrobeniusAt σ ℓ₀ ∧ LinearMap.trace k ρbar.V (ρbar.ρ σ) ≠ (ℓ₀ : k) + 1 := by
  obtain ⟨ℓ₀, hℓ₀, hS, hN, hmodp, hsq, A, σ, hA, hσ, hne⟩ :=
    exists_prime_notMem_not_dvd_modEq_one_trace_frobenius_ne_two p hp2 N S k ρbar hirr
  have hℓk : ((ℓ₀ : ℕ) : k) = 1 := by
    have h1 : ((ℓ₀ : ℕ) : k) = ((1 : ℕ) : k) := (CharP.natCast_eq_natCast k p).mpr hmodp
    rw [h1, Nat.cast_one]
  refine ⟨ℓ₀, hℓ₀, hS, hN, hsq, A, σ, hA, hσ, ?_⟩
  rw [hℓk]
  norm_num
  exact hne

end ResidualGaloisRep

end PieceWitness

section PieceClimb

namespace CohCarrier
p2m_export "CohCarrier" "coresAdd mem_Gamma0Upper gamma0Units val_gamma0Units GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_11 GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conj_mem_GammaH conjHom diamondRaw LevelLE iotaDeg iDeg' iotaDeg_injective pushChar jDeg coe_iotaDeg_one heckeT_comp_coeff coeff_comp_smul_eq_zero jDeg_heckeT_comm_flat iDeg_heckeT_comm_of_coprime heckeT_comm_of_prime heckeT_diamondRaw_comm exists_gamma0_lift_dvd transfer_restrict_eq_pow_index index_GammaHUpper_of_prime heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms"
p2m_open "CohCarrier"

open CongruenceSubgroup
open scoped MatrixGroups

section Engine

variable {G : Type*} [Group G]

private theorem smul_eq_self_of_mem {K : Subgroup G} [hN : K.Normal] {k : G} (hk : k ∈ K) (q : G ⧸ K) :
    k • q = q := by
  induction q using QuotientGroup.induction_on with
  | H t =>
    change ((k * t : G) : G ⧸ K) = (t : G ⧸ K)
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hN.conj_mem' k⁻¹ (K.inv_mem hk) t

private theorem coresAdd_apply_of_mem (K : Subgroup G) [hN : K.Normal] [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ : Additive ↥K →+ B) (T : K.LeftTransversal) {k : G} (hk : k ∈ K) :
    haveI := K.fintypeQuotientOfFiniteIndex
    coresAdd K φ (Additive.ofMul k) =
      ∑ q : G ⧸ K, φ (Additive.ofMul
        (⟨(T.2.leftQuotientEquiv q : G)⁻¹ * k * (T.2.leftQuotientEquiv q : G),
          hN.conj_mem' k hk (T.2.leftQuotientEquiv q : G)⟩ : ↥K)) := by
  simp only [coresAdd, MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.transfer_def _ T,
    Subgroup.leftTransversals.diff, toAdd_prod, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 2
  apply Subtype.ext
  have h : ((k • T).2.leftQuotientEquiv q : G) = k * (T.2.leftQuotientEquiv q : G) := by
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_self_of_mem (K.inv_mem hk), smul_eq_mul]
  show (T.2.leftQuotientEquiv q : G)⁻¹ * ((k • T).2.leftQuotientEquiv q : G) =
    (T.2.leftQuotientEquiv q : G)⁻¹ * k * (T.2.leftQuotientEquiv q : G)
  rw [h, mul_assoc]

end Engine

section SameLevel

variable (M : ℕ) [NeZero M] (Hc Hf : Subgroup (ZMod M)ˣ) (A : Type*) [AddCommGroup A]
  (h : LevelLE M M Hc Hf 1)

private def toGamma0Inv (g : ↥(GammaH M Hc)) : Gamma0 M :=
  ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 M).inv_mem (GammaH_le_Gamma0 Hc g.2)⟩

omit [NeZero M] in

private theorem range_iotaDeg_one_normal : (iotaDeg M M Hc Hf 1 h).range.Normal := by
  refine ⟨fun y hy g => ?_⟩
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
  refine MonoidHom.mem_range.mpr ⟨conjHom M Hf (toGamma0Inv M Hc g⁻¹) x, ?_⟩
  apply Subtype.ext
  rw [coe_iotaDeg_one h]
  simp [conjHom, toGamma0Inv, coe_iotaDeg_one h]

omit [NeZero M] in

private theorem iotaDeg_one_conjHom_toGamma0Inv (t : ↥(GammaH M Hc)) (x : ↥(GammaH M Hf)) :
    iotaDeg M M Hc Hf 1 h (conjHom M Hf (toGamma0Inv M Hc t) x) = t⁻¹ * iotaDeg M M Hc Hf 1 h x * t := by
  apply Subtype.ext
  rw [coe_iotaDeg_one h]
  show (t : SL(2, ℤ))⁻¹ * (x : SL(2, ℤ)) * ((t : SL(2, ℤ))⁻¹)⁻¹ =
    ((t⁻¹ * iotaDeg M M Hc Hf 1 h x * t : ↥(GammaH M Hc)) : SL(2, ℤ))
  rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_iotaDeg_one h]

private theorem iDeg'_jDeg_eq_index_smul_of_diamondRaw_eq (v : H1 M Hf A)
    (hv : ∀ σ : Gamma0 M, diamondRaw M Hf A σ v = v) :
    iDeg' M M Hc Hf 1 A h (jDeg M M Hc Hf 1 A h v) = (iotaDeg M M Hc Hf 1 h).range.index • v := by
  haveI := range_iotaDeg_one_normal M Hc Hf h
  letI := (iotaDeg M M Hc Hf 1 h).range.fintypeQuotientOfFiniteIndex
  ext x
  show coresAdd _ (pushChar M M Hc Hf 1 A h v) (Additive.ofMul (iotaDeg M M Hc Hf 1 h (Additive.toMul x))) =
    (iotaDeg M M Hc Hf 1 h).range.index • v x
  rw [coresAdd_apply_of_mem _ _ default (MonoidHom.mem_range.mpr ⟨_, rfl⟩)]
  have key : ∀ q : ↥(GammaH M Hc) ⧸ (iotaDeg M M Hc Hf 1 h).range,
      pushChar M M Hc Hf 1 A h v (Additive.ofMul
        (⟨((default : (iotaDeg M M Hc Hf 1 h).range.LeftTransversal).2.leftQuotientEquiv q : ↥(GammaH M Hc))⁻¹ *
            iotaDeg M M Hc Hf 1 h (Additive.toMul x) *
            ((default : (iotaDeg M M Hc Hf 1 h).range.LeftTransversal).2.leftQuotientEquiv q : ↥(GammaH M Hc)),
          (range_iotaDeg_one_normal M Hc Hf h).conj_mem' _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _⟩ :
            ↥(iotaDeg M M Hc Hf 1 h).range)) = v x := by
    intro q
    set t : ↥(GammaH M Hc) :=
      ((default : (iotaDeg M M Hc Hf 1 h).range.LeftTransversal).2.leftQuotientEquiv q : ↥(GammaH M Hc))
    have hsymm : ((iotaDeg M M Hc Hf 1 h).ofInjective (iotaDeg_injective M M Hc Hf 1 h)).symm
        (⟨t⁻¹ * iotaDeg M M Hc Hf 1 h (Additive.toMul x) * t,
          (range_iotaDeg_one_normal M Hc Hf h).conj_mem' _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _⟩ :
            ↥(iotaDeg M M Hc Hf 1 h).range) =
        conjHom M Hf (toGamma0Inv M Hc t) (Additive.toMul x) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [MonoidHom.ofInjective_apply, iotaDeg_one_conjHom_toGamma0Inv]
    show v (Additive.ofMul (((iotaDeg M M Hc Hf 1 h).ofInjective (iotaDeg_injective M M Hc Hf 1 h)).symm _)) = v x
    rw [toMul_ofMul, hsymm]
    exact congrArg (fun w : H1 M Hf A => w x) (hv (toGamma0Inv M Hc t))
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_const, Finset.card_univ, Subgroup.index,
    Nat.card_eq_fintype_card]

omit [NeZero M] in

private theorem iDeg'_diamondRaw_comm (σ : Gamma0 M) (z : H1 M Hc A) :
    iDeg' M M Hc Hf 1 A h (diamondRaw M Hc A σ z) = diamondRaw M Hf A σ (iDeg' M M Hc Hf 1 A h z) := by
  ext x
  show z (Additive.ofMul (conjHom M Hc σ (iotaDeg M M Hc Hf 1 h (Additive.toMul x)))) =
    z (Additive.ofMul (iotaDeg M M Hc Hf 1 h (conjHom M Hf σ (Additive.toMul x))))
  congr 2
  apply Subtype.ext
  rw [coe_iotaDeg_one h]
  show (σ : SL(2, ℤ)) * ((iotaDeg M M Hc Hf 1 h (Additive.toMul x) : ↥(GammaH M Hc)) : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ =
    (σ : SL(2, ℤ)) * ((Additive.toMul x : ↥(GammaH M Hf)) : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹
  rw [coe_iotaDeg_one h]

end SameLevel

end CohCarrier

namespace CohCarrier
p2m_export "CohCarrier" "coresAdd mem_Gamma0Upper gamma0Units val_gamma0Units GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_11 GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conj_mem_GammaH conjHom diamondRaw LevelLE iotaDeg iDeg' iotaDeg_injective pushChar jDeg coe_iotaDeg_one heckeT_comp_coeff coeff_comp_smul_eq_zero jDeg_heckeT_comm_flat iDeg_heckeT_comm_of_coprime heckeT_comm_of_prime heckeT_diamondRaw_comm exists_gamma0_lift_dvd transfer_restrict_eq_pow_index index_GammaHUpper_of_prime heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms"
namespace CharacterSwitch
p2m_open "CohCarrier"

p2m_open "CongruenceSubgroup CohCarrier P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible.CohCarrier"
open scoped MatrixGroups

private theorem toAdditiveLeft_pow {G V : Type*} [Group G] [AddCommGroup V] (f : G →* Multiplicative V) (n : ℕ) :
    MonoidHom.toAdditiveLeft (f ^ n) = n • MonoidHom.toAdditiveLeft f := by
  ext g
  simp [MonoidHom.pow_apply, toAdd_pow]

variable {N : ℕ} {H H' : Subgroup (ZMod N)ˣ} {V : Type*} [AddCommGroup V]

private theorem mul_inv_mem_of_apply_eq (γ δ : ↥(GammaH N H'))
    (h : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) :
    ((γ * δ⁻¹ : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H := by
  have hγ : (γ : SL(2, ℤ)) ∈ Gamma0 N := GammaH_le_Gamma0 H' γ.2
  have hδ : (δ : SL(2, ℤ)) ∈ Gamma0 N := GammaH_le_Gamma0 H' δ.2
  have hmem : ((γ * δ⁻¹ : ↥(GammaH N H')) : SL(2, ℤ)) ∈ Gamma0 N := GammaH_le_Gamma0 H' (γ * δ⁻¹).2
  refine mem_GammaH_iff.mpr ⟨hmem, ?_⟩
  have hsplit : (⟨_, hmem⟩ : Gamma0 N) = (⟨γ, hγ⟩ : Gamma0 N) * (⟨δ, hδ⟩ : Gamma0 N)⁻¹ := by
    apply Subtype.ext
    simp
  have hunits : gamma0Units N ⟨γ, hγ⟩ = gamma0Units N ⟨δ, hδ⟩ := by
    ext
    simp only [val_gamma0Units, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [h]
  rw [hsplit, map_mul, map_inv, hunits, mul_inv_cancel]
  exact H.one_mem

private theorem apply_conjL_eq (ℓ : ℕ) (z : H1 N H' V)
    (hz : ∀ γ : ↥(GammaH N H'), (γ : SL(2, ℤ)) ∈ GammaH N H → z (Additive.ofMul γ) = 0)
    (γ : ↥(GammaHUpper N H' ℓ)) :
    z (Additive.ofMul (conjL N H' ℓ γ)) = z (Additive.ofMul (γ : ↥(GammaH N H'))) := by
  have hentry : (((conjL N H' ℓ γ : ↥(GammaH N H')) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
      (((γ : ↥(GammaH N H')) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 :=
    conjUpperMat_apply_11 ℓ (γ : SL(2, ℤ)) (dvd_of_mem_GammaHUpper N H' ℓ γ)
  have h0 := hz _ (mul_inv_mem_of_apply_eq (H := H) (conjL N H' ℓ γ) (γ : ↥(GammaH N H')) hentry)
  rw [ofMul_mul, ofMul_inv, map_add, map_neg, add_neg_eq_zero] at h0
  exact h0

private theorem heckeT_apply_eq_index_smul (ℓ : ℕ) [NeZero ℓ] (z : H1 N H' V)
    (hz : ∀ γ : ↥(GammaH N H'), (γ : SL(2, ℤ)) ∈ GammaH N H → z (Additive.ofMul γ) = 0) :
    heckeT N H' ℓ V z = (GammaHUpper N H' ℓ).index • z := by
  have hcomp : (AddMonoidHom.toMultiplicativeRight z).comp (conjL N H' ℓ) =
      (AddMonoidHom.toMultiplicativeRight z).domRestrict (GammaHUpper N H' ℓ) := by
    ext γ
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.restrict_apply,
      AddMonoidHom.toMultiplicativeRight_apply_apply]
    rw [apply_conjL_eq (H := H) ℓ z hz γ]
  show MonoidHom.toAdditiveLeft
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight z).comp (conjL N H' ℓ))) = _
  rw [hcomp, CohCarrier.transfer_restrict_eq_pow_index, toAdditiveLeft_pow]
  congr 1

private theorem heckeT_apply_eq_succ_nsmul (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (z : H1 N H' V)
    (hz : ∀ γ : ↥(GammaH N H'), (γ : SL(2, ℤ)) ∈ GammaH N H → z (Additive.ofMul γ) = 0) :
    heckeT N H' ℓ V z = (ℓ + 1) • z := by
  rw [heckeT_apply_eq_index_smul (H := H) ℓ z hz, CohCarrier.index_GammaHUpper_of_prime N H' ℓ hℓ hℓN]

private theorem heckeT_apply_eq_succ_smul {k : Type*} [CommRing k] [Module k V] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) (z : H1 N H' V)
    (hz : ∀ γ : ↥(GammaH N H'), (γ : SL(2, ℤ)) ∈ GammaH N H → z (Additive.ofMul γ) = 0) :
    heckeT N H' ℓ V z = ((ℓ : k) + 1) • z := by
  rw [heckeT_apply_eq_succ_nsmul (H := H) ℓ hℓ hℓN z hz, ← Nat.cast_smul_eq_nsmul k, Nat.cast_succ]

private theorem eq_zero_of_heckeT_eq_smul {p : ℕ} {k : Type*} [Field k] [CharP k p] [Module k V] (ℓ : ℕ) [NeZero ℓ]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n - (ℓ + 1)) (z : H1 N H' V)
    (hz : ∀ γ : ↥(GammaH N H'), (γ : SL(2, ℤ)) ∈ GammaH N H → z (Additive.ofMul γ) = 0)
    (hT : heckeT N H' ℓ V z = (n : k) • z) : z = 0 := by
  have hE := heckeT_apply_eq_succ_smul (H := H) (k := k) ℓ hℓ hℓN z hz
  have hdiff : (((n - (ℓ + 1) : ℤ)) : k) • z = 0 := by
    have : ((n : k) - ((ℓ : k) + 1)) • z = 0 := by
      rw [sub_smul, ← hT, hE, sub_self]
    push_cast
    exact this
  have hne : (((n - (ℓ + 1) : ℤ)) : k) ≠ 0 := by
    rw [Ne, CharP.intCast_eq_zero_iff k p]
    exact hn
  exact (smul_eq_zero.mp hdiff).resolve_left hne

private theorem apply_eq_zero_of_iDeg'_eq_zero [NeZero N] (h : LevelLE N N H' H 1) (z : H1 N H' V)
    (hz : iDeg' N N H' H 1 V h z = 0) (γ : ↥(GammaH N H')) (hγ : (γ : SL(2, ℤ)) ∈ GammaH N H) :
    z (Additive.ofMul γ) = 0 := by
  have hιγ : iotaDeg N N H' H 1 h ⟨(γ : SL(2, ℤ)), hγ⟩ = γ := Subtype.ext (coe_iotaDeg_one h _)
  have h0 := congrArg (fun w : H1 N H V => w (Additive.ofMul (⟨(γ : SL(2, ℤ)), hγ⟩ : ↥(GammaH N H)))) hz
  simp only [AddMonoidHom.zero_apply] at h0
  rw [← hιγ]
  exact h0

private theorem heckeT_apply_eq_succ_smul_of_iDeg'_eq_zero [NeZero N] {k : Type*} [CommRing k] [Module k V]
    (h : LevelLE N N H' H 1) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (z : H1 N H' V)
    (hz : iDeg' N N H' H 1 V h z = 0) :
    heckeT N H' ℓ V z = ((ℓ : k) + 1) • z :=
  heckeT_apply_eq_succ_smul (H := H) (k := k) ℓ hℓ hℓN z (apply_eq_zero_of_iDeg'_eq_zero h z hz)

private theorem eq_zero_of_iDeg'_eq_zero_of_heckeT_eq_smul [NeZero N] {p : ℕ} {k : Type*} [Field k] [CharP k p]
    [Module k V] (h : LevelLE N N H' H 1) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℤ)
    (hn : ¬ (p : ℤ) ∣ n - (ℓ + 1)) (z : H1 N H' V) (hz : iDeg' N N H' H 1 V h z = 0)
    (hT : heckeT N H' ℓ V z = (n : k) • z) : z = 0 :=
  eq_zero_of_heckeT_eq_smul (H := H) ℓ hℓ hℓN n hn z (apply_eq_zero_of_iDeg'_eq_zero h z hz) hT

end CohCarrier.CharacterSwitch

open scoped MatrixGroups

open CongruenceSubgroup

namespace CohCarrier
p2m_export "CohCarrier" "coresAdd mem_Gamma0Upper gamma0Units val_gamma0Units GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjUpperMat conjUpperMat_apply_11 GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conj_mem_GammaH conjHom diamondRaw LevelLE iotaDeg iDeg' iotaDeg_injective pushChar jDeg coe_iotaDeg_one heckeT_comp_coeff coeff_comp_smul_eq_zero jDeg_heckeT_comm_flat iDeg_heckeT_comm_of_coprime heckeT_comm_of_prime heckeT_diamondRaw_comm exists_gamma0_lift_dvd transfer_restrict_eq_pow_index index_GammaHUpper_of_prime heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms"
p2m_open "CohCarrier"

namespace InvariantExtension

section Transfer

variable {G : Type*} [Group G] {K : Subgroup G} [K.Normal] [K.FiniteIndex] {B : Type*} [AddCommGroup B]

private theorem coresAdd_apply_eq_apply_pow_index (φ : Additive ↥K →+ B)
    (hφ : ∀ (g k : G) (hk : k ∈ K) (hk' : g⁻¹ * k * g ∈ K),
      φ (Additive.ofMul ⟨g⁻¹ * k * g, hk'⟩) = φ (Additive.ofMul ⟨k, hk⟩))
    (g : G) :
    coresAdd K φ (Additive.ofMul g) = φ (Additive.ofMul ⟨g ^ K.index, K.pow_index_mem g⟩) := by
  classical
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ K))) := Fintype.ofFinite _
  have hmem : ∀ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ K)),
      g ^ Function.minimalPeriod (g • ·) q.out ∈ K := by
    intro q
    have h2 := ‹K.Normal›.mem_comm (QuotientGroup.out_conj_pow_minimalPeriod_mem K g q.out)
    rwa [mul_inv_cancel_left] at h2
  have hval : ∀ x : ↥K, Multiplicative.toAdd (AddMonoidHom.toMultiplicativeRight φ x) = φ (Additive.ofMul x) :=
    fun x => rfl

  have hsum : ∀ (m : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ K)) → ℕ) (hm : ∀ q, g ^ m q ∈ K)
      (s : Finset (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ K))))
      (hs : g ^ (∑ q ∈ s, m q) ∈ K),
      ∑ q ∈ s, φ (Additive.ofMul ⟨g ^ m q, hm q⟩) = φ (Additive.ofMul ⟨g ^ (∑ q ∈ s, m q), hs⟩) := by
    intro m hm s
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      rw [Finset.sum_empty]
      have e : (⟨g ^ (∑ q ∈ (∅ : Finset _), m q), hs⟩ : ↥K) = 1 :=
        Subtype.ext (by
          show g ^ (∑ q ∈ (∅ : Finset _), m q) = 1
          rw [Finset.sum_empty, pow_zero])
      rw [e, ofMul_one, map_zero]
    | insert a s ha ih =>
      intro hs
      have hs' : g ^ (∑ q ∈ s, m q) ∈ K := by
        have h1 := mul_mem (inv_mem (hm a)) hs
        rwa [Finset.sum_insert ha, pow_add, inv_mul_cancel_left] at h1
      rw [Finset.sum_insert ha, ih hs']
      have e : (⟨g ^ (∑ q ∈ insert a s, m q), hs⟩ : ↥K) = ⟨g ^ m a, hm a⟩ * ⟨g ^ (∑ q ∈ s, m q), hs'⟩ :=
        Subtype.ext (by
          show g ^ (∑ q ∈ insert a s, m q) = g ^ m a * g ^ (∑ q ∈ s, m q)
          rw [Finset.sum_insert ha, pow_add])
      rw [e, ofMul_mul, map_add]
  have hidx : g ^ (∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ K)),
      Function.minimalPeriod (g • ·) q.out) ∈ K := by
    rw [← Subgroup.index_eq_sum_minimalPeriod K g]
    exact K.pow_index_mem g
  show Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ) g) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  calc ∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ K)),
        Multiplicative.toAdd (AddMonoidHom.toMultiplicativeRight φ
          ⟨q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem K g q.out⟩)
      = ∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ K)),
          φ (Additive.ofMul ⟨g ^ Function.minimalPeriod (g • ·) q.out, hmem q⟩) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hval]
        exact hφ q.out.out _ (hmem q) _
    _ = φ (Additive.ofMul ⟨g ^ (∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ K)),
          Function.minimalPeriod (g • ·) q.out), hidx⟩) := hsum _ hmem _ hidx
    _ = φ (Additive.ofMul ⟨g ^ K.index, K.pow_index_mem g⟩) := by
        congr 2
        apply Subtype.ext
        show g ^ _ = g ^ K.index
        rw [Subgroup.index_eq_sum_minimalPeriod K g]

end Transfer

section Pair

variable {N : ℕ} [NeZero N] {H H' : Subgroup (ZMod N)ˣ} (h : LevelLE N N H' H 1)

omit [NeZero N] in

private theorem mem_range_iotaDeg_one_iff (x : ↥(GammaH N H')) :
    x ∈ (iotaDeg N N H' H 1 h).range ↔ (x : SL(2, ℤ)) ∈ GammaH N H := by
  constructor
  · rintro ⟨γ, rfl⟩
    rw [coe_iotaDeg_one]
    exact γ.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subtype.ext (coe_iotaDeg_one h ⟨x, hx⟩)⟩

omit [NeZero N] in

private theorem iotaDeg_one_eq (γ : ↥(GammaH N H)) (hγ : (γ : SL(2, ℤ)) ∈ GammaH N H') :
    iotaDeg N N H' H 1 h γ = ⟨γ, hγ⟩ :=
  Subtype.ext (coe_iotaDeg_one h γ)

omit [NeZero N] in

private theorem pushChar_apply_eq {V : Type} [AddCommGroup V] (v : H1 N H V) (x : ↥(GammaH N H'))
    (hx : x ∈ (iotaDeg N N H' H 1 h).range) (hx' : (x : SL(2, ℤ)) ∈ GammaH N H) :
    pushChar N N H' H 1 V h v (Additive.ofMul ⟨x, hx⟩) = v (Additive.ofMul ⟨x, hx'⟩) := by
  have e : (⟨x, hx⟩ : ↥(iotaDeg N N H' H 1 h).range) =
      MonoidHom.ofInjective (iotaDeg_injective N N H' H 1 h) ⟨x, hx'⟩ :=
    Subtype.ext (iotaDeg_one_eq h ⟨x, hx'⟩ x.2).symm
  show v (Additive.ofMul ((MonoidHom.ofInjective (iotaDeg_injective N N H' H 1 h)).symm ⟨x, hx⟩)) = _
  rw [e, MulEquiv.symm_apply_apply]

omit [NeZero N] in

private theorem apply_conj_eq {V : Type} [AddCommGroup V] (v : H1 N H V)
    (hinv : ∀ σ : Gamma0 N, diamondRaw N H V σ v = v) (σ : Gamma0 N) (γ : ↥(GammaH N H))
    (hc : (σ : SL(2, ℤ)) * γ * (σ : SL(2, ℤ))⁻¹ ∈ GammaH N H) :
    v (Additive.ofMul ⟨(σ : SL(2, ℤ)) * γ * (σ : SL(2, ℤ))⁻¹, hc⟩) = v (Additive.ofMul γ) := by
  conv_rhs => rw [← hinv σ]
  rfl

private theorem jDeg_apply_eq_apply_pow_index {V : Type} [AddCommGroup V] (v : H1 N H V)
    (hinv : ∀ σ : Gamma0 N, diamondRaw N H V σ v = v) (g : ↥(GammaH N H'))
    (hg : (((g ^ (iotaDeg N N H' H 1 h).range.index : ↥(GammaH N H')) : SL(2, ℤ))) ∈ GammaH N H) :
    jDeg N N H' H 1 V h v (Additive.ofMul g) =
      v (Additive.ofMul ⟨((g ^ (iotaDeg N N H' H 1 h).range.index : ↥(GammaH N H')) : SL(2, ℤ)),
        hg⟩) := by
  haveI := range_iotaDeg_one_normal N H' H h
  show coresAdd _ (pushChar N N H' H 1 V h v) (Additive.ofMul g) = _
  rw [coresAdd_apply_eq_apply_pow_index]
  · exact pushChar_apply_eq h v _ _ hg
  · intro g₀ k hk hk'
    have hkm : (k : SL(2, ℤ)) ∈ GammaH N H := (mem_range_iotaDeg_one_iff h k).mp hk
    have hkm' : ((g₀⁻¹ * k * g₀ : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H :=
      (mem_range_iotaDeg_one_iff h _).mp hk'
    rw [pushChar_apply_eq h v _ hk' hkm', pushChar_apply_eq h v _ hk hkm]
    have hσ : ((g₀ : SL(2, ℤ)))⁻¹ ∈ Gamma0 N := inv_mem (GammaH_le_Gamma0 H' g₀.2)
    have hc : ((⟨_, hσ⟩ : Gamma0 N) : SL(2, ℤ)) * ((⟨(k : SL(2, ℤ)), hkm⟩ : ↥(GammaH N H)) : SL(2, ℤ)) *
        ((⟨_, hσ⟩ : Gamma0 N) : SL(2, ℤ))⁻¹ ∈ GammaH N H := by
      simpa using hkm'
    have := apply_conj_eq v hinv ⟨_, hσ⟩ ⟨(k : SL(2, ℤ)), hkm⟩ hc
    rw [← this]
    congr 2
    apply Subtype.ext
    simp [mul_assoc]

private theorem index_dvd_of_zpow_mem {G : Type*} [Group G] {K : Subgroup G} [K.Normal] (g : G)
    (hgen : ∀ x : G, ∃ n : ℤ, x * g ^ n ∈ K) (n : ℤ) (hn : g ^ n ∈ K) : (K.index : ℤ) ∣ n := by
  have hcyc : ∀ y : G ⧸ K, y ∈ Subgroup.zpowers (g : G ⧸ K) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨m, hm⟩ := hgen x
      have e : (x : G ⧸ K) = ((g : G ⧸ K)) ^ (-m) := by
        rw [zpow_neg, eq_inv_iff_mul_eq_one, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
          QuotientGroup.eq_one_iff]
        exact hm
      rw [e]
      exact Subgroup.zpow_mem_zpowers _ _
  have hord : orderOf (g : G ⧸ K) = K.index := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hcyc, Subgroup.index_eq_card]
  rw [← hord, orderOf_dvd_iff_zpow_eq_one, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
  exact hn

omit [NeZero N] in

private theorem exists_iDeg'_eq {V : Type} [AddCommGroup V] (g : ↥(GammaH N H'))
    (hgen : ∀ x : ↥(GammaH N H'), ∃ n : ℤ, ((x * g ^ n : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H)
    (v : H1 N H V) (hinv : ∀ σ : Gamma0 N, diamondRaw N H V σ v = v)
    (hvan : ∀ (n : ℤ) (hn : ((g ^ n : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H),
      v (Additive.ofMul ⟨_, hn⟩) = 0) :
    ∃ w : H1 N H' V, iDeg' N N H' H 1 V h w = v := by
  classical

  have indep : ∀ (x : ↥(GammaH N H')) (n n' : ℤ)
      (hn : ((x * g ^ n : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H)
      (hn' : ((x * g ^ n' : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H),
      v (Additive.ofMul ⟨_, hn⟩) = v (Additive.ofMul ⟨_, hn'⟩) := by
    intro x n n' hn hn'
    have hd : ((g ^ (n' - n) : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H := by
      have : g ^ (n' - n) = (x * g ^ n)⁻¹ * (x * g ^ n') := by group
      rw [this, Subgroup.coe_mul, Subgroup.coe_inv]
      exact mul_mem (inv_mem hn) hn'
    have e0 : x * g ^ n' = (x * g ^ n) * g ^ (n' - n) := by group
    have e : (⟨((x * g ^ n' : ↥(GammaH N H')) : SL(2, ℤ)), hn'⟩ : ↥(GammaH N H)) =
        ⟨((x * g ^ n : ↥(GammaH N H')) : SL(2, ℤ)), hn⟩ * ⟨((g ^ (n' - n) : ↥(GammaH N H')) : SL(2, ℤ)), hd⟩ :=
      Subtype.ext (by
        show ((x * g ^ n' : ↥(GammaH N H')) : SL(2, ℤ)) = _
        rw [e0]
        rfl)
    rw [e, ofMul_mul, map_add, hvan (n' - n) hd, add_zero]

  let nx : ↥(GammaH N H') → ℤ := fun x => (hgen x).choose
  have hnx : ∀ x, ((x * g ^ nx x : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H := fun x => (hgen x).choose_spec
  let w₀ : ↥(GammaH N H') → V := fun x => v (Additive.ofMul ⟨_, hnx x⟩)
  have hw₀ : ∀ (x : ↥(GammaH N H')) (n : ℤ) (hn : ((x * g ^ n : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H),
      w₀ x = v (Additive.ofMul ⟨_, hn⟩) := fun x n hn => indep x (nx x) n (hnx x) hn
  have hmul : ∀ x y : ↥(GammaH N H'), w₀ (x * y) = w₀ x + w₀ y := by
    intro x y

    have hσ : (((g ^ (-nx x) : ↥(GammaH N H')) : SL(2, ℤ))) ∈ Gamma0 N := GammaH_le_Gamma0 H' (g ^ (-nx x)).2
    have hconj := conj_mem_GammaH N H ⟨_, hσ⟩ ⟨_, hnx y⟩
    have hprod : ((x * y * g ^ (nx x + nx y) : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H := by
      have e : x * y * g ^ (nx x + nx y) =
          (x * g ^ nx x) * (g ^ (-nx x) * (y * g ^ nx y) * (g ^ (-nx x))⁻¹) := by group
      rw [e, Subgroup.coe_mul]
      refine mul_mem (hnx x) ?_
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj
    rw [hw₀ (x * y) (nx x + nx y) hprod]
    have e0 : x * y * g ^ (nx x + nx y) =
        (x * g ^ nx x) * (g ^ (-nx x) * (y * g ^ nx y) * (g ^ (-nx x))⁻¹) := by group
    have e : (⟨((x * y * g ^ (nx x + nx y) : ↥(GammaH N H')) : SL(2, ℤ)), hprod⟩ : ↥(GammaH N H)) =
        ⟨_, hnx x⟩ * ⟨_, hconj⟩ :=
      Subtype.ext (by
        show ((x * y * g ^ (nx x + nx y) : ↥(GammaH N H')) : SL(2, ℤ)) = _
        rw [e0]
        rfl)
    rw [e, ofMul_mul, map_add]
    show w₀ x + v (Additive.ofMul ⟨_, hconj⟩) = w₀ x + w₀ y
    rw [apply_conj_eq v hinv ⟨_, hσ⟩ ⟨_, hnx y⟩ hconj]
  refine ⟨AddMonoidHom.mk' (fun a => w₀ (Additive.toMul a)) (fun a b => hmul _ _), ?_⟩
  apply AddMonoidHom.ext
  intro a
  show w₀ (iotaDeg N N H' H 1 h (Additive.toMul a)) = v a
  have h0 : (((iotaDeg N N H' H 1 h (Additive.toMul a)) * g ^ (0 : ℤ) : ↥(GammaH N H')) : SL(2, ℤ)) ∈
      GammaH N H := by
    rw [zpow_zero, mul_one, coe_iotaDeg_one]
    exact (Additive.toMul a).2
  rw [hw₀ _ 0 h0]
  show v (Additive.ofMul _) = v (Additive.ofMul (Additive.toMul a))
  congr 2
  apply Subtype.ext
  simpa only [zpow_zero, mul_one] using coe_iotaDeg_one h (Additive.toMul a)

end Pair

section Step

private theorem natCast_zsmul_eq_zero {p : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod p) W] (x : W) :
    (p : ℤ) • x = 0 := by
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

variable {p : ℕ} [Fact p.Prime] {N : ℕ} [NeZero N] {H H' : Subgroup (ZMod N)ˣ} (h : LevelLE N N H' H 1)
  {V : Type} [AddCommGroup V]

private theorem exists_mul_eq_one_add (c : ℤ) (hc : ¬ (p : ℤ) ∣ c) : ∃ e t : ℤ, e * c = 1 + p * t := by
  have hp : p.Prime := Fact.out
  have hg : Int.gcd c p = 1 := by
    rcases (Nat.dvd_prime hp).mp (Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right c p)) with h1 | h2
    · exact h1
    · exfalso
      apply hc
      have h3 := Int.gcd_dvd_left c p
      rwa [h2] at h3
  have hb := Int.gcd_eq_gcd_ab c p
  rw [hg, Nat.cast_one] at hb
  exact ⟨Int.gcdA c p, -Int.gcdB c p, by linarith⟩

variable [Module (ZMod p) V]

private theorem eq_zero_of_iDeg'_eq_zero {ℓ : ℕ} [NeZero ℓ]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {c : ℤ} (hne : ¬ (p : ℤ) ∣ c - (ℓ + 1 : ℕ)) (z : H1 N H' V)
    (hz : iDeg' N N H' H 1 V h z = 0) (hT : heckeT N H' ℓ V z = c • z) : z = 0 := by
  have hE := CharacterSwitch.heckeT_apply_eq_succ_nsmul (H := H) ℓ hℓ hℓN z
    (CharacterSwitch.apply_eq_zero_of_iDeg'_eq_zero h z hz)
  rw [hT] at hE

  have h1 : (c - (ℓ + 1 : ℕ)) • z = 0 := by
    rw [sub_zsmul, hE, add_neg_eq_zero]
    norm_cast
  obtain ⟨e, t, het⟩ := exists_mul_eq_one_add (p := p) _ hne
  have h2 : (e * (c - (ℓ + 1 : ℕ))) • z = 0 := by rw [mul_zsmul, h1, zsmul_zero]
  rw [het, add_zsmul, one_zsmul, mul_zsmul, natCast_zsmul_eq_zero (p := p), add_zero] at h2
  exact h2

private theorem step (g : ↥(GammaH N H'))
    (hgen : ∀ x : ↥(GammaH N H'), ∃ n : ℤ, ((x * g ^ n : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H)
    (S : Finset ℕ) (n : ℕ → ℤ) (v : H1 N H V) (hinv : ∀ σ : Gamma0 N, diamondRaw N H V σ v = v)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      heckeT N H ℓ V v = n ℓ • v)
    {ℓ₀ : ℕ} (hℓ₀ : ℓ₀.Prime) (hℓ₀S : ℓ₀ ∉ S) (hℓ₀N : ¬ ℓ₀ ∣ N)
    (hne : ¬ (p : ℤ) ∣ n ℓ₀ - (ℓ₀ + 1 : ℕ)) :
    ∃ w : H1 N H' V, iDeg' N N H' H 1 V h w = v ∧ (∀ σ : Gamma0 N, diamondRaw N H' V σ w = w) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        heckeT N H' ℓ V w = n ℓ • w := by
  classical
  haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI := range_iotaDeg_one_normal N H' H h
  have hT₀ : heckeT N H ℓ₀ V v = n ℓ₀ • v := hT ℓ₀ hℓ₀ hℓ₀S hℓ₀N
  set K := (iotaDeg N N H' H 1 h).range with hK

  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : H1 N H' V, iDeg' N N H' H 1 V h w₁ = v := by
    have hres : iDeg' N N H' H 1 V h (jDeg N N H' H 1 V h v) = K.index • v :=
      iDeg'_jDeg_eq_index_smul_of_diamondRaw_eq N H' H V h v hinv
    by_cases hm : ((K.index : ℕ) : ZMod p) = 0
    ·
      have hz : iDeg' N N H' H 1 V h (jDeg N N H' H 1 V h v) = 0 := by
        obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff K.index p).mp hm
        rw [hres, ← natCast_zsmul, ht, Nat.cast_mul, mul_zsmul, natCast_zsmul_eq_zero (p := p)]
      have hTz : heckeT N H' ℓ₀ V (jDeg N N H' H 1 V h v) = n ℓ₀ • jDeg N N H' H 1 V h v := by
        rw [jDeg_heckeT_comm_flat h (Nat.coprime_one_right ℓ₀) hℓ₀ hℓ₀N, hT₀, map_zsmul]
      have hj : jDeg N N H' H 1 V h v = 0 := eq_zero_of_iDeg'_eq_zero h hℓ₀ hℓ₀N hne _ hz hTz
      refine exists_iDeg'_eq h g hgen v hinv fun m hm' => ?_
      have hgm : g ^ m ∈ K := (mem_range_iotaDeg_one_iff h _).mpr hm'
      obtain ⟨e, rfl⟩ := index_dvd_of_zpow_mem g
        (fun x => by
          obtain ⟨k, hk⟩ := hgen x
          exact ⟨k, (mem_range_iotaDeg_one_iff h _).mpr hk⟩) _ hgm
      have hidx : (((g ^ K.index : ↥(GammaH N H')) : SL(2, ℤ))) ∈ GammaH N H :=
        (mem_range_iotaDeg_one_iff h _).mp (K.pow_index_mem g)
      have hval := jDeg_apply_eq_apply_pow_index h v hinv g hidx
      rw [hj, AddMonoidHom.zero_apply] at hval
      have e : (⟨((g ^ ((K.index : ℤ) * e) : ↥(GammaH N H')) : SL(2, ℤ)), hm'⟩ : ↥(GammaH N H)) =
          ⟨((g ^ K.index : ↥(GammaH N H')) : SL(2, ℤ)), hidx⟩ ^ e := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, zpow_mul, zpow_natCast]
        rfl
      rw [e, ofMul_zpow, map_zsmul, ← hval, zsmul_zero]
    ·
      obtain ⟨e, t, het⟩ : ∃ e t : ℤ, e * K.index = 1 + p * t := by
        refine exists_mul_eq_one_add (p := p) _ fun hd => hm ?_
        rw [← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hd
      refine ⟨e • jDeg N N H' H 1 V h v, ?_⟩
      rw [map_zsmul, hres, ← natCast_zsmul, ← mul_zsmul, het, add_zsmul, one_zsmul, mul_zsmul,
        natCast_zsmul_eq_zero (p := p), add_zero]

  let F : H1 N H' V →+ H1 N H' V := heckeT N H' ℓ₀ V - n ℓ₀ • AddMonoidHom.id _
  have hF : ∀ w, F w = heckeT N H' ℓ₀ V w - n ℓ₀ • w := fun w => rfl
  have hFres : iDeg' N N H' H 1 V h (F w₁) = 0 := by
    rw [hF, map_sub, map_zsmul, iDeg_heckeT_comm_of_coprime h (Nat.coprime_one_right ℓ₀) hℓ₀ hℓ₀N, hw₁,
      hT₀, sub_self]
  have hFE : ∀ z : H1 N H' V, iDeg' N N H' H 1 V h z = 0 → F z = (((ℓ₀ + 1 : ℕ) : ℤ) - n ℓ₀) • z := by
    intro z hz
    rw [hF, CharacterSwitch.heckeT_apply_eq_succ_nsmul (H := H) ℓ₀ hℓ₀ hℓ₀N z
      (CharacterSwitch.apply_eq_zero_of_iDeg'_eq_zero h z hz), sub_zsmul, ← sub_eq_add_neg, sub_left_inj]
    norm_cast
  obtain ⟨e, t, het⟩ : ∃ e t : ℤ, e * (((ℓ₀ + 1 : ℕ) : ℤ) - n ℓ₀) = 1 + p * t := by
    refine exists_mul_eq_one_add (p := p) _ fun hd => hne ?_
    have : n ℓ₀ - ((ℓ₀ + 1 : ℕ) : ℤ) = -(((ℓ₀ + 1 : ℕ) : ℤ) - n ℓ₀) := by ring
    rw [this]
    exact (dvd_neg).mpr hd
  set w := w₁ - e • F w₁ with hwdef
  have hwres : iDeg' N N H' H 1 V h w = v := by
    rw [hwdef, map_sub, map_zsmul, hFres, zsmul_zero, sub_zero, hw₁]
  have hw₀ : heckeT N H' ℓ₀ V w = n ℓ₀ • w := by
    rw [← sub_eq_zero, ← hF, hwdef, map_sub, map_zsmul, hFE (F w₁) hFres, ← mul_zsmul, het, add_zsmul,
      one_zsmul, mul_zsmul, natCast_zsmul_eq_zero (p := p), add_zero, sub_self]
  clear_value w

  have crit : ∀ z : H1 N H' V, iDeg' N N H' H 1 V h z = 0 → heckeT N H' ℓ₀ V z = n ℓ₀ • z → z = 0 :=
    fun z hz hTz => eq_zero_of_iDeg'_eq_zero h hℓ₀ hℓ₀N hne z hz hTz
  refine ⟨w, hwres, ?_, ?_⟩
  ·
    intro σ
    obtain ⟨σ', hσ', hdvd⟩ := exists_gamma0_lift_dvd N ℓ₀ (gamma0Units N σ)

    have hσ'w : diamondRaw N H' V σ' w = w := by
      rw [← sub_eq_zero]
      apply crit
      · rw [map_sub, iDeg'_diamondRaw_comm N H' H V h, hwres, hinv, sub_self]
      · rw [map_sub, heckeT_diamondRaw_comm N H' ℓ₀ σ' hdvd, hw₀, map_zsmul, zsmul_sub]

    have hκ : (σ : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹ ∈ GammaH N H' := by
      refine mem_GammaH_iff.mpr ⟨mul_mem σ.2 (inv_mem σ'.2), ?_⟩
      have : (⟨(σ : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹, mul_mem σ.2 (inv_mem σ'.2)⟩ : Gamma0 N) = σ * σ'⁻¹ := rfl
      rw [this, map_mul, map_inv, hσ', mul_inv_cancel]
      exact one_mem _
    apply AddMonoidHom.ext
    intro a
    conv_rhs => rw [← hσ'w]
    show w (Additive.ofMul (conjHom N H' σ (Additive.toMul a))) =
      w (Additive.ofMul (conjHom N H' σ' (Additive.toMul a)))
    have e : conjHom N H' σ (Additive.toMul a) =
        ⟨_, hκ⟩ * conjHom N H' σ' (Additive.toMul a) * (⟨_, hκ⟩ : ↥(GammaH N H'))⁻¹ := by
      apply Subtype.ext
      show (σ : SL(2, ℤ)) * ((Additive.toMul a : ↥(GammaH N H')) : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ =
        (σ : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹ *
          ((σ' : SL(2, ℤ)) * ((Additive.toMul a : ↥(GammaH N H')) : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹) *
          ((σ : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹)⁻¹
      group
    rw [e, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel
  ·
    intro ℓ hℓ hℓS hℓN
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    by_cases hℓℓ₀ : ℓ = ℓ₀
    · subst hℓℓ₀
      exact hw₀
    rw [← sub_eq_zero]
    apply crit
    · rw [map_sub, map_zsmul, iDeg_heckeT_comm_of_coprime h (Nat.coprime_one_right ℓ) hℓ hℓN, hwres,
        hT ℓ hℓ hℓS hℓN, sub_self]
    · have hcop : Nat.Coprime ℓ₀ ℓ := (Nat.coprime_primes hℓ₀ hℓ).mpr (Ne.symm hℓℓ₀)
      rw [map_sub, map_zsmul, heckeT_comm_of_prime N H' ℓ₀ ℓ hℓ₀ hcop, hw₀, map_zsmul, zsmul_sub]
      congr 1
      rw [← mul_zsmul, ← mul_zsmul, mul_comm]

end Step

section Climb

variable {p : ℕ} [Fact p.Prime] {N : ℕ} [NeZero N]

omit [NeZero N] in

private theorem levelLE_of_le {H H' : Subgroup (ZMod N)ˣ} (hle : H ≤ H') : LevelLE N N H' H 1 :=
  ⟨dvd_rfl, by simp, fun u hu => by rw [ZMod.unitsMap_self]; exact hle hu⟩

private theorem exists_iDeg'_eq_of_diamondRaw_eq_of_heckeT_eq {H : Subgroup (ZMod N)ˣ} (h : LevelLE N N ⊤ H 1)
    (S : Finset ℕ) (n : ℕ → ℤ) {V : Type} [AddCommGroup V] [Module (ZMod p) V] (v : H1 N H V)
    (hinv : ∀ σ : Gamma0 N, diamondRaw N H V σ v = v)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      heckeT N H ℓ V v = n ℓ • v)
    {ℓ₀ : ℕ} (hℓ₀ : ℓ₀.Prime) (hℓ₀S : ℓ₀ ∉ S) (hℓ₀N : ¬ ℓ₀ ∣ N)
    (hne : ¬ (p : ℤ) ∣ n ℓ₀ - (ℓ₀ + 1 : ℕ)) :
    ∃ w : H1 N ⊤ V, iDeg' N N ⊤ H 1 V h w = v ∧ (∀ σ : Gamma0 N, diamondRaw N ⊤ V σ w = w) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        heckeT N ⊤ ℓ V w = n ℓ • w := by
  classical
  suffices key : ∀ (d : ℕ) (H : Subgroup (ZMod N)ˣ), H.index = d → ∀ (h : LevelLE N N ⊤ H 1)
      (v : H1 N H V), (∀ σ : Gamma0 N, diamondRaw N H V σ v = v) →
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        heckeT N H ℓ V v = n ℓ • v) →
      ∃ w : H1 N ⊤ V, iDeg' N N ⊤ H 1 V h w = v ∧ (∀ σ : Gamma0 N, diamondRaw N ⊤ V σ w = w) ∧
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          heckeT N ⊤ ℓ V w = n ℓ • w from
    key _ H rfl h v hinv hT
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro H hd h v hinv hT
    by_cases hH : H = ⊤
    · subst hH
      refine ⟨v, ?_, hinv, hT⟩
      apply AddMonoidHom.ext
      intro a
      show v (Additive.ofMul (iotaDeg N N ⊤ ⊤ 1 h (Additive.toMul a))) = v (Additive.ofMul (Additive.toMul a))
      congr 2
      exact Subtype.ext (coe_iotaDeg_one h (Additive.toMul a))

    obtain ⟨u, -, hu⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH)
    set H' : Subgroup (ZMod N)ˣ := H ⊔ Subgroup.zpowers u with hH'
    have hle : H ≤ H' := le_sup_left
    have hlt : H'.index < H.index := by
      have hmul := Subgroup.relIndex_mul_index hle
      have hne1 : H.relIndex H' ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        intro hle'
        exact hu (hle' (Subgroup.mem_sup_right (Subgroup.mem_zpowers u)))
      have hne0 : H.relIndex H' ≠ 0 := by
        show (H.subgroupOf H').index ≠ 0
        exact Subgroup.index_ne_zero_of_finite
      have hidx : H'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 : 2 ≤ H.relIndex H' := by omega
      calc H'.index < 2 * H'.index := by omega
        _ ≤ H.relIndex H' * H'.index := Nat.mul_le_mul_right _ h2
        _ = H.index := hmul
    have h₁ : LevelLE N N H' H 1 := levelLE_of_le hle
    have h₂ : LevelLE N N ⊤ H' 1 := levelLE_of_le le_top

    obtain ⟨σ, hσu, -⟩ := exists_gamma0_lift_dvd N 1 u
    have hσ : (σ : SL(2, ℤ)) ∈ GammaH N H' := by
      refine mem_GammaH_iff.mpr ⟨σ.2, ?_⟩
      rw [Subtype.coe_eta, hσu]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    set g : ↥(GammaH N H') := ⟨σ, hσ⟩ with hg
    have hgen : ∀ x : ↥(GammaH N H'), ∃ m : ℤ, ((x * g ^ m : ↥(GammaH N H')) : SL(2, ℤ)) ∈ GammaH N H := by
      intro x
      obtain ⟨hx0, hxH'⟩ := mem_GammaH_iff.mp x.2
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hxH'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine ⟨-k, mem_GammaH_iff.mpr ⟨(GammaH_le_Gamma0 H' (x * g ^ (-k)).2), ?_⟩⟩
      have e : (⟨((x * g ^ (-k) : ↥(GammaH N H')) : SL(2, ℤ)), GammaH_le_Gamma0 H' (x * g ^ (-k)).2⟩ :
          Gamma0 N) = ⟨(x : SL(2, ℤ)), hx0⟩ * σ ^ (-k) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
        rfl
      rw [e, map_mul, map_zpow, hσu, ← hyz, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
      exact hy
    obtain ⟨w', hw'res, hw'inv, hw'T⟩ := step h₁ g hgen S n v hinv hT hℓ₀ hℓ₀S hℓ₀N hne
    obtain ⟨w, hwres, hwinv, hwT⟩ := IH _ (hd ▸ hlt) H' rfl h₂ w' hw'inv hw'T
    refine ⟨w, ?_, hwinv, hwT⟩
    rw [← hw'res, ← hwres]
    apply AddMonoidHom.ext
    intro a
    show w (Additive.ofMul (iotaDeg N N ⊤ H 1 h (Additive.toMul a))) =
      w (Additive.ofMul (iotaDeg N N ⊤ H' 1 h₂ (iotaDeg N N H' H 1 h₁ (Additive.toMul a))))
    congr 2
    apply Subtype.ext
    rw [coe_iotaDeg_one, coe_iotaDeg_one, coe_iotaDeg_one]

end Climb

end InvariantExtension

end CohCarrier

end PieceClimb

section PieceFiniteOrder

namespace TraceOfFiniteOrder

p2m_open "Matrix~trace_pow_add_two"

section MatrixLemmas

variable (A : Matrix (Fin 2) (Fin 2) ℤ)

private theorem mul_self_eq (hA : A.det = 1) : A * A = A.trace • A - 1 := by
  rw [Matrix.det_fin_two] at hA
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.trace_fin_two]
  fin_cases i <;> fin_cases j <;> simp <;> linarith

private theorem det_neg_eq (hA : A.det = 1) : (-A).det = 1 := by
  rw [Matrix.det_neg, Fintype.card_fin, hA]; norm_num

private theorem pow_add_two (hA : A.det = 1) (k : ℕ) :
    A ^ (k + 2) = A.trace • A ^ (k + 1) - A ^ k := by
  have h : A ^ (k + 2) = A ^ k * (A * A) := by
    rw [pow_succ, pow_succ, mul_assoc]
  rw [h, mul_self_eq A hA, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← pow_succ]

private theorem trace_pow_add_two (hA : A.det = 1) (k : ℕ) :
    (A ^ (k + 2)).trace = A.trace * (A ^ (k + 1)).trace - (A ^ k).trace := by
  rw [pow_add_two A hA k, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]

private theorem trace_pow_ge (hA : A.det = 1) (h3 : 3 ≤ A.trace) (k : ℕ) :
    2 ≤ (A ^ k).trace ∧ (A ^ k).trace + 1 ≤ (A ^ (k + 1)).trace := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [Matrix.trace_one]
    · simp only [pow_zero, zero_add, pow_one, Matrix.trace_one, Fintype.card_fin]
      push_cast
      omega
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨by omega, ?_⟩
    rw [trace_pow_add_two A hA k]
    have hpos : (0 : ℤ) ≤ (A ^ (k + 1)).trace := by omega
    have hmul := mul_le_mul_of_nonneg_right h3 hpos
    nlinarith

private theorem pow_ne_one_of_three_le_trace (hA : A.det = 1) (h3 : 3 ≤ A.trace) {n : ℕ}
    (hn : 0 < n) : A ^ n ≠ 1 := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := (trace_pow_ge A hA h3 m)
  have htr : (A ^ (m + 1)).trace = 2 := by
    rw [h, Matrix.trace_one, Fintype.card_fin]; norm_num
  omega

private theorem eq_one_of_pow_eq_one_of_trace_eq_two (hA : A.det = 1) (ht : A.trace = 2) {n : ℕ}
    (hn : 0 < n) (h : A ^ n = 1) : A = 1 := by
  set ν : Matrix (Fin 2) (Fin 2) ℤ := A - 1 with hν
  have hsq : ν * ν = 0 := by
    have h2 := mul_self_eq A hA
    rw [ht, two_smul] at h2
    rw [hν, sub_mul, mul_sub, mul_sub, h2]
    noncomm_ring
  have hpow : ∀ m : ℕ, A ^ m = 1 + (m : ℤ) • ν := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hA' : A = 1 + ν := by rw [hν]; abel
      rw [pow_succ, ih, hA', add_mul, mul_add, mul_add, one_mul, one_mul, mul_one,
        Matrix.smul_mul, hsq, smul_zero, add_zero]
      push_cast
      rw [add_smul, one_smul]
      abel
  have hν0 : (n : ℤ) • ν = 0 := by
    have := hpow n
    rw [h] at this
    exact (add_eq_left.mp this.symm)
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have : ν = 0 := by
    ext i j
    have hij := congrFun (congrFun hν0 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, mul_eq_zero] at hij
    exact hij.resolve_left hn'
  rw [hν] at this
  exact sub_eq_zero.mp this

end MatrixLemmas

section SpecialLinearGroup

variable (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)

private theorem coe_pow_eq_one {n : ℕ} (h : γ ^ n = 1) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ n = 1 := by
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℤ => (g : Matrix (Fin 2) (Fin 2) ℤ)) h
  simpa using this

private theorem trace_mem_of_isOfFinOrder (hγ : IsOfFinOrder γ) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = -2 ∨ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = -1 ∨
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 0 ∨ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 ∨
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hγ
  set A : Matrix (Fin 2) (Fin 2) ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hAdef
  have hA : A.det = 1 := γ.det_coe
  have hAn : A ^ n = 1 := coe_pow_eq_one γ hpow
  by_cases hbig : 3 ≤ A.trace
  · exact absurd hAn (pow_ne_one_of_three_le_trace A hA hbig hn)
  by_cases hsmall : A.trace ≤ -3
  · exfalso
    have hB : (-A).det = 1 := det_neg_eq A hA
    have hBt : 3 ≤ (-A).trace := by rw [Matrix.trace_neg]; omega
    have hBn : (-A) ^ (2 * n) = 1 := by
      rw [Even.neg_pow (even_two_mul n), mul_comm, pow_mul, hAn, one_pow]
    exact pow_ne_one_of_three_le_trace (-A) hB hBt (by omega) hBn
  omega

private theorem eq_one_of_isOfFinOrder_of_trace_eq_two (hγ : IsOfFinOrder γ)
    (ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) : γ = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hγ
  exact Subtype.ext (eq_one_of_pow_eq_one_of_trace_eq_two _ γ.det_coe ht hn (coe_pow_eq_one γ hpow))

private theorem eq_neg_one_of_isOfFinOrder_of_trace_eq_neg_two (hγ : IsOfFinOrder γ)
    (ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = -2) : γ = -1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hγ
  set A : Matrix (Fin 2) (Fin 2) ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hAdef
  have hA : A.det = 1 := γ.det_coe
  have hAn : A ^ n = 1 := coe_pow_eq_one γ hpow
  have hB : (-A).det = 1 := det_neg_eq A hA
  have hBt : (-A).trace = 2 := by rw [Matrix.trace_neg, ht]; norm_num
  have hBn : (-A) ^ (2 * n) = 1 := by
    rw [Even.neg_pow (even_two_mul n), mul_comm, pow_mul, hAn, one_pow]
  have hB1 : -A = 1 := eq_one_of_pow_eq_one_of_trace_eq_two (-A) hB hBt (by omega) hBn
  have hA1 : A = -(1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    have h := congrFun (congrFun hB1 i) j
    rw [Matrix.neg_apply] at h
    rw [Matrix.neg_apply, ← h, neg_neg]
  exact Subtype.ext hA1

private theorem sq_eq_neg_one_of_trace_eq_zero (ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 0) :
    γ ^ 2 = -1 := by
  apply Subtype.ext
  change (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = -(1 : Matrix (Fin 2) (Fin 2) ℤ)
  rw [pow_two, mul_self_eq _ γ.det_coe, ht, zero_smul, zero_sub]

private theorem pow_three_eq_one_of_trace_eq_neg_one (ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = -1) :
    γ ^ 3 = 1 := by
  apply Subtype.ext
  change (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ 3 = (1 : Matrix (Fin 2) (Fin 2) ℤ)
  have h2 := mul_self_eq _ γ.det_coe
  rw [ht, neg_one_smul] at h2
  rw [pow_succ, pow_two, h2, sub_mul, neg_mul, one_mul, h2]
  noncomm_ring

private theorem pow_three_eq_neg_one_of_trace_eq_one (ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 1) :
    γ ^ 3 = -1 := by
  apply Subtype.ext
  change (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ 3 = -(1 : Matrix (Fin 2) (Fin 2) ℤ)
  have h2 := mul_self_eq _ γ.det_coe
  rw [ht, one_smul] at h2
  rw [pow_succ, pow_two, h2, sub_mul, one_mul, h2]
  noncomm_ring

end SpecialLinearGroup

end TraceOfFiniteOrder

end PieceFiniteOrder

section PieceEllipticTransfer

open scoped MatrixGroups
open CongruenceSubgroup Matrix.SpecialLinearGroup

namespace EllipticTransfer

private theorem sq_add_add_one_ne_zero (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : ℓ % 3 = 2) (a : ZMod ℓ) :
    a * a + a + 1 ≠ 0 := by
  intro h
  have hp : ℓ.Prime := Fact.out
  have ha3 : a ^ 3 = 1 := by
    have h' : a ^ 3 - 1 = (a - 1) * (a * a + a + 1) := by ring
    rw [← sub_eq_zero, h', h, mul_zero]
  have ha1 : a ≠ 1 := by
    rintro rfl
    have h3 : ((3 : ℕ) : ZMod ℓ) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h3
    have h33 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at h
  have hl1 : a ^ (ℓ - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
  have hg : a ^ Nat.gcd 3 (ℓ - 1) = 1 := pow_gcd_eq_one.mpr ⟨ha3, hl1⟩
  have hcop : Nat.Coprime 3 (ℓ - 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  rw [hcop.gcd_eq_one, pow_one] at hg
  exact ha1 hg

private theorem coe_mul_self_eq (γ : SL(2, ℤ)) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ) * γ
      = (γ : Matrix (Fin 2) (Fin 2) ℤ).trace • (γ : Matrix (Fin 2) (Fin 2) ℤ) - 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.trace_fin_two, Matrix.one_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    simp <;>
    first | ring1 | linear_combination (-1 : ℤ) * hdet

private theorem cube_eq_of_trace (γ : SL(2, ℤ))
    (htr : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 ∨ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = -1) :
    γ ^ 3 = 1 ∨ γ ^ 3 = -1 := by
  have hsq := coe_mul_self_eq γ
  have hcube : ∀ t : ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = t → t * t = 1 →
      (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ 3 = -(t • (1 : Matrix (Fin 2) (Fin 2) ℤ)) := by
    intro t ht ht2
    rw [ht] at hsq
    rw [pow_three, hsq, mul_sub, mul_one, Matrix.mul_smul, hsq, smul_sub, smul_smul, ht2, one_smul]
    abel
  rcases htr with h | h
  · right
    apply Subtype.ext
    rw [coe_pow, hcube 1 h (by norm_num), one_smul, coe_neg, coe_one]
  · left
    apply Subtype.ext
    rw [coe_pow, hcube (-1) h (by norm_num), neg_smul, neg_neg, one_smul, coe_one]

private theorem conjUpperMat_eq_self (ℓ : ℕ) (B : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ B 0 1) (hB : B = 1 ∨ B = -1) :
    CohCarrier.conjUpperMat ℓ B h = B := by
  rcases hB with rfl | rfl <;>
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjUpperMat]

private theorem heckeT_apply_eq_zero_of_trace (M : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : ℓ % 3 = 2)
    {A : Type} [AddCommGroup A] (F : CohCarrier.H1 M ⊤ A) (g : ↥(CohCarrier.GammaH M ⊤))
    (htr : ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 ∨
      ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = -1)
    (hF : F (Additive.ofMul (g ^ 3)) = 0) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    CohCarrier.heckeT M ⊤ ℓ A F (Additive.ofMul g) = 0 := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  classical

  set K : Subgroup ↥(CohCarrier.GammaH M ⊤) := CohCarrier.GammaHUpper M ⊤ ℓ with hK
  set ϕ : ↥K →* Multiplicative A :=
    (AddMonoidHom.toMultiplicativeRight F).comp (CohCarrier.conjL M ⊤ ℓ) with hϕ

  have hcube : (g : SL(2, ℤ)) ^ 3 = 1 ∨ (g : SL(2, ℤ)) ^ 3 = -1 := cube_eq_of_trace _ htr
  have hcoe : ((g ^ 3 : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) = 1 ∨
      ((g ^ 3 : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) = -1 := by
    simpa only [SubgroupClass.coe_pow] using hcube

  have hcent : ∀ t : ↥(CohCarrier.GammaH M ⊤), t⁻¹ * g ^ 3 * t = g ^ 3 := by
    intro t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rcases hcoe with h | h <;> rw [h]
    · rw [mul_one, inv_mul_cancel]
    · rw [mul_neg, mul_one, neg_mul, inv_mul_cancel]
  have hmem : g ^ 3 ∈ K := by
    rw [hK, Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper]
    rcases hcoe with h | h <;> rw [h]
    · simp
    · simp [coe_neg]

  have hnot : ∀ t : ↥(CohCarrier.GammaH M ⊤), t⁻¹ * g * t ∉ K := by
    intro t ht
    rw [hK, Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper] at ht
    set κ : SL(2, ℤ) := ((t⁻¹ * g * t : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) with hκ
    have hκ' : κ = (t : SL(2, ℤ))⁻¹ * (g : SL(2, ℤ)) * (t : SL(2, ℤ)) := by
      rw [hκ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have htrκ : (κ : Matrix (Fin 2) (Fin 2) ℤ).trace = ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
      rw [hκ', coe_mul, coe_mul, Matrix.trace_mul_cycle, ← coe_mul, mul_inv_cancel, coe_one, one_mul]
    have hdet := Matrix.SpecialLinearGroup.det_coe κ
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.trace_fin_two] at htrκ
    have hb : ((κ 0 1 : ℤ) : ZMod ℓ) = 0 := ht
    have hd : ((κ 0 0 : ℤ) : ZMod ℓ) * ((κ 1 1 : ℤ) : ZMod ℓ) = 1 := by
      have h := congrArg (fun z : ℤ => (z : ZMod ℓ)) hdet
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
      rw [hb, zero_mul, sub_zero] at h
      exact h
    rcases htr with h1 | h1 <;> rw [h1] at htrκ
    · have hs : ((κ 0 0 : ℤ) : ZMod ℓ) + ((κ 1 1 : ℤ) : ZMod ℓ) = 1 := by
        have h := congrArg (fun z : ℤ => (z : ZMod ℓ)) htrκ
        simp only [Int.cast_add, Int.cast_one] at h
        exact h
      exact sq_add_add_one_ne_zero ℓ hℓ3 (-((κ 0 0 : ℤ) : ZMod ℓ))
        (by linear_combination ((κ 0 0 : ℤ) : ZMod ℓ) * hs - hd)
    · have hs : ((κ 0 0 : ℤ) : ZMod ℓ) + ((κ 1 1 : ℤ) : ZMod ℓ) = -1 := by
        have h := congrArg (fun z : ℤ => (z : ZMod ℓ)) htrκ
        simp only [Int.cast_add, Int.cast_neg, Int.cast_one] at h
        exact h
      exact sq_add_add_one_ne_zero ℓ hℓ3 ((κ 0 0 : ℤ) : ZMod ℓ)
        (by linear_combination ((κ 0 0 : ℤ) : ZMod ℓ) * hs - hd)

  have hper : ∀ x : ↥(CohCarrier.GammaH M ⊤) ⧸ K, Function.minimalPeriod (g • ·) x = 3 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H t =>
      have h3 : g ^ 3 • (t : ↥(CohCarrier.GammaH M ⊤) ⧸ K) = (t : ↥(CohCarrier.GammaH M ⊤) ⧸ K) := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
        have h' : (g ^ 3 * t)⁻¹ * t = (t⁻¹ * g ^ 3 * t)⁻¹ := by group
        rw [h', hcent]
        exact K.inv_mem hmem
      have hdvd : Function.minimalPeriod (g • ·) (t : ↥(CohCarrier.GammaH M ⊤) ⧸ K) ∣ 3 :=
        MulAction.pow_smul_eq_iff_minimalPeriod_dvd.mp h3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exfalso
        rw [Function.minimalPeriod_eq_one_iff_isFixedPt, Function.IsFixedPt,
          MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h1
        have h' : (g * t)⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
        rw [h'] at h1
        have h2 := K.inv_mem h1
        rw [inv_inv] at h2
        exact hnot t h2
      · exact h1

  have hval : ∀ k : ↥K, (k : ↥(CohCarrier.GammaH M ⊤)) = g ^ 3 → ϕ k = 1 := by
    intro k hk
    have hk' : ((k : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) = 1 ∨
        ((k : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) = -1 := by
      rw [hk]; exact hcoe
    have hc : CohCarrier.conjL M ⊤ ℓ k = (k : ↥(CohCarrier.GammaH M ⊤)) :=
      Subtype.ext (conjUpperMat_eq_self ℓ ((k : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ))
        (CohCarrier.dvd_of_mem_GammaHUpper M ⊤ ℓ k) hk')
    rw [hϕ, MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, hc, hk, hF]
    rfl

  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (↥(CohCarrier.GammaH M ⊤) ⧸ K))) :=
    Fintype.ofFinite _
  show Multiplicative.toAdd (MonoidHom.transfer ϕ g) = 0
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot ϕ g,
    Finset.prod_eq_one (fun q _ => hval _ (by
      show (Quotient.out (Quotient.out q))⁻¹ * g ^ Function.minimalPeriod (g • ·) (Quotient.out q)
          * Quotient.out (Quotient.out q) = g ^ 3
      rw [hper]
      exact hcent _)), toAdd_one]

end EllipticTransfer

end PieceEllipticTransfer

section PieceSliceThree

namespace TraceVanishingCoset

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem pair_linearIndependent_of_notMem_span {x y : V} (hx : x ≠ 0) (hy : y ∉ Submodule.span K {x}) :
    LinearIndependent K ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    apply hy
    rw [Submodule.mem_span_singleton]
    refine ⟨-(s / t), ?_⟩
    have : t • y = -(s • x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
    calc (-(s / t)) • x = t⁻¹ • (-(s • x)) := by rw [neg_smul, smul_neg, smul_smul, div_eq_inv_mul]
      _ = t⁻¹ • (t • y) := by rw [this]
      _ = y := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  subst ht
  simp only [zero_smul, add_zero, smul_eq_zero] at hst
  exact ⟨hst.resolve_right hx, rfl⟩

private theorem exists_notMem_span_singleton (hV : finrank K V = 2) (x : V) :
    ∃ y : V, y ∉ Submodule.span K {x} := by
  by_contra hcon
  have h : ∀ y, y ∈ Submodule.span K {x} := fun y => by_contra fun hy => hcon ⟨y, hy⟩
  have htop : Submodule.span K {x} = ⊤ := Submodule.eq_top_iff'.mpr h
  have h1 : finrank K (Submodule.span K {x}) ≤ 1 := by
    simpa using finrank_span_le_card ({x} : Set V)
  rw [htop, finrank_top, hV] at h1
  omega

private theorem span_singleton_ne_bot_ne_top_stable (hV : finrank K V = 2) {v : V} (hv : v ≠ 0)
    (S : Set (Module.End K V)) (hS : ∀ f ∈ S, ∃ μ : K, f v = μ • v) :
    ∃ L : Submodule K V, L ≠ ⊥ ∧ L ≠ ⊤ ∧ ∀ f ∈ S, ∀ x ∈ L, f x ∈ L := by
  refine ⟨Submodule.span K {v}, ?_, ?_, ?_⟩
  · rwa [Ne, Submodule.span_singleton_eq_bot]
  · intro htop
    have h1 := finrank_span_singleton (K := K) hv
    rw [htop, finrank_top, hV] at h1
    omega
  · intro f hf x hx
    obtain ⟨μ, hμ⟩ := hS f hf
    rw [Submodule.mem_span_singleton] at hx ⊢
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t * μ, by rw [map_smul, hμ, smul_smul]⟩

variable [IsAlgClosed K] {G : Type*} [Group G]

private theorem exists_basis_eigen (hV : finrank K V = 2) (h2 : (2 : K) ≠ 0) (Z : Module.End K V)
    (hZinj : Function.Injective Z) (htr : LinearMap.trace K V Z = 0) :
    ∃ (b : Basis (Fin 2) K V) (α : K), α ≠ 0 ∧ Z (b 0) = α • b 0 ∧ Z (b 1) = (-α) • b 1 := by
  haveI : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hV]; norm_num)
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue Z
  obtain ⟨u, hu⟩ := hα.exists_hasEigenvector
  have hu0 : u ≠ 0 := hu.2
  have hZu : Z u = α • u := hu.apply_eq_smul
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hZu
    exact hu0 (hZinj (by rw [hZu, map_zero]))
  obtain ⟨w, hw⟩ := exists_notMem_span_singleton hV u
  have hli : LinearIndependent K ![u, w] := pair_linearIndependent_of_notMem_span hu0 hw
  let b₁ : Basis (Fin 2) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have hb₁ : ⇑b₁ = ![u, w] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hb₁0 : b₁ 0 = u := by rw [hb₁]; rfl
  have hb₁1 : b₁ 1 = w := by rw [hb₁]; rfl

  set β : K := b₁.repr (Z w) 0 with hβ
  set γ : K := b₁.repr (Z w) 1 with hγ
  have hZw : Z w = β • u + γ • w := by
    have := b₁.sum_repr (Z w)
    rw [Fin.sum_univ_two, hb₁0, hb₁1] at this
    exact this.symm

  have hru : b₁.repr u 0 = 1 := by rw [← hb₁0, b₁.repr_self]; simp
  have htrace : α + γ = 0 := by
    have h := htr
    rw [LinearMap.trace_eq_matrix_trace K b₁, Matrix.trace_fin_two, LinearMap.toMatrix_apply,
      LinearMap.toMatrix_apply, hb₁0, hb₁1, hZu, map_smul, Finsupp.smul_apply, hru, smul_eq_mul,
      mul_one] at h
    exact h
  have hγα : γ = -α := by linear_combination htrace

  set u' : V := Z w - α • w with hu'
  have hu'eq : u' = β • u + (-(2 * α)) • w := by
    rw [hu', hZw, hγα]; module
  have hZu' : Z u' = (-α) • u' := by
    rw [hu'eq, map_add, map_smul, map_smul, hZu, hZw, hγα]; module
  have hli' : LinearIndependent K ![u, u'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [hu'eq] at hst
    have hst' : (s + t * β) • u + (t * (-(2 * α))) • w = 0 := by
      rw [← hst]; module
    obtain ⟨h1, h2'⟩ := LinearIndependent.pair_iff.mp hli _ _ hst'
    have ht : t = 0 := by
      rcases mul_eq_zero.mp h2' with h | h
      · exact h
      · exact absurd h (by simpa [h2] using hα0)
    subst ht
    exact ⟨by simpa using h1, rfl⟩
  let b : Basis (Fin 2) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli' (by rw [Fintype.card_fin, hV])
  have hb : ⇑b = ![u, u'] := coe_basisOfLinearIndependentOfCardEqFinrank hli' _
  refine ⟨b, α, hα0, ?_, ?_⟩
  · rw [show b 0 = u by rw [hb]; rfl]; exact hZu
  · rw [show b 1 = u' by rw [hb]; rfl]; exact hZu'

private theorem exists_submodule_ne_bot_ne_top_of_forall_notMem_trace_eq_zero (hV : finrank K V = 2)
    (h2 : (2 : K) ≠ 0) (ρ : G →* Module.End K V) (H : Subgroup G) {z : G} (hz : z ∉ H)
    (htr : ∀ g : G, g ∉ H → LinearMap.trace K V (ρ g) = 0) :
    ∃ L : Submodule K V, L ≠ ⊥ ∧ L ≠ ⊤ ∧ ∀ h ∈ H, ∀ x ∈ L, ρ h x ∈ L := by

  have hZinj : Function.Injective (ρ z) := by
    intro x y hxy
    have := congrArg (ρ z⁻¹) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, Module.End.one_apply] at this
  obtain ⟨b, α, hα0, hb0, hb1⟩ := exists_basis_eigen hV h2 (ρ z) hZinj (htr z hz)

  set A : G → Matrix (Fin 2) (Fin 2) K := fun g => LinearMap.toMatrix b b (ρ g) with hA
  have hAmul : ∀ g g' : G, A (g * g') = A g * A g' := fun g g' => by
    simp only [hA, map_mul, LinearMap.toMatrix_mul]
  have hAtr : ∀ g : G, LinearMap.trace K V (ρ g) = (A g).trace := fun g =>
    LinearMap.trace_eq_matrix_trace K b (ρ g)
  have hAz : ∀ i j, A z i j = if i = j then (if i = 0 then α else -α) else 0 := by
    intro i j
    simp only [hA, LinearMap.toMatrix_apply]
    fin_cases i <;> fin_cases j <;> simp [hb0, hb1, Basis.repr_self]

  have hzh : ∀ h ∈ H, z * h ∉ H := fun h hh hzh => hz (by simpa using H.mul_mem hzh (H.inv_mem hh))

  have hdiag : ∀ h ∈ H, A h 0 0 = A h 1 1 := by
    intro h hh
    have := htr (z * h) (hzh h hh)
    rw [hAtr, hAmul, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, hAz, hAz, hAz, hAz] at this
    simp only [if_true, if_false, zero_mul, add_zero, zero_add, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      neg_mul, Fin.isValue, one_ne_zero] at this
    have : α * (A h 0 0 - A h 1 1) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hα0
    · linear_combination h'

  have hoff : ∀ h ∈ H, ∀ h' ∈ H, A h 0 1 * A h' 1 0 = A h 1 0 * A h' 0 1 := by
    intro h hh h' hh'
    have htr' := htr (z * (h * h')) (hzh _ (H.mul_mem hh hh'))
    rw [hAtr, hAmul, hAmul, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, hAz, hAz, hAz, hAz] at htr'
    simp only [if_true, if_false, zero_mul, add_zero, zero_add, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      neg_mul, Fin.isValue, one_ne_zero, Matrix.mul_apply, Fin.sum_univ_two] at htr'
    have hd := hdiag h hh
    have hd' := hdiag h' hh'
    have : α * (A h 0 1 * A h' 1 0 - A h 1 0 * A h' 0 1) = 0 := by
      linear_combination htr' - α * (A h' 0 0) * hd - α * (A h 1 1) * hd'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hα0
    · linear_combination h0

  have happly : ∀ (h : G) (x y : K), ρ h (x • b 0 + y • b 1) =
      (A h 0 0 * x + A h 0 1 * y) • b 0 + (A h 1 0 * x + A h 1 1 * y) • b 1 := by
    intro h x y
    have key : ∀ j, ρ h (b j) = A h 0 j • b 0 + A h 1 j • b 1 := by
      intro j
      have := b.sum_repr (ρ h (b j))
      rw [Fin.sum_univ_two] at this
      rw [← this]
      simp only [hA, LinearMap.toMatrix_apply]
    rw [map_add, map_smul, map_smul, key 0, key 1]; module

  by_cases hcase : ∀ h ∈ H, A h 1 0 = 0
  ·
    refine span_singleton_ne_bot_ne_top_stable hV (b.ne_zero 0) {f | ∃ h ∈ H, f = ρ h} ?_ |>.imp
      fun L hL => ⟨hL.1, hL.2.1, fun h hh x hx => hL.2.2 (ρ h) ⟨h, hh, rfl⟩ x hx⟩
    rintro f ⟨h, hh, rfl⟩
    refine ⟨A h 0 0, ?_⟩
    have := happly h 1 0
    rw [one_smul, zero_smul, add_zero] at this
    rw [this, hcase h hh]; simp
  · obtain ⟨h₀, hh₀, hc₀⟩ : ∃ h₀ ∈ H, A h₀ 1 0 ≠ 0 := by
      simpa only [not_forall, exists_prop] using hcase
    obtain ⟨δ, hδ⟩ : ∃ δ : K, δ * δ = A h₀ 0 1 * A h₀ 1 0 := by
      obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (A h₀ 0 1 * A h₀ 1 0) two_pos
      exact ⟨δ, by rw [← hδ]; ring⟩
    have hv0 : δ • b 0 + A h₀ 1 0 • b 1 ≠ 0 := by
      intro h0
      have h1 := congrArg (fun x => b.repr x 1) h0
      exact hc₀ (by simpa [Finsupp.single_apply] using h1)
    refine span_singleton_ne_bot_ne_top_stable hV hv0 {f | ∃ h ∈ H, f = ρ h} ?_ |>.imp
      fun L hL => ⟨hL.1, hL.2.1, fun h hh x hx => hL.2.2 (ρ h) ⟨h, hh, rfl⟩ x hx⟩
    rintro f ⟨h, hh, rfl⟩
    have hprop : A h 0 1 * A h₀ 1 0 = A h 1 0 * A h₀ 0 1 := hoff h hh h₀ hh₀
    have hd : A h 1 1 = A h 0 0 := (hdiag h hh).symm
    refine ⟨(A h 1 0 * δ + A h 1 1 * A h₀ 1 0) / A h₀ 1 0, ?_⟩
    have e1 : (A h 1 0 * δ + A h 1 1 * A h₀ 1 0) / A h₀ 1 0 * A h₀ 1 0 = A h 1 0 * δ + A h 1 1 * A h₀ 1 0 :=
      div_mul_cancel₀ _ hc₀
    have e0 : (A h 1 0 * δ + A h 1 1 * A h₀ 1 0) / A h₀ 1 0 * δ = A h 0 0 * δ + A h 0 1 * A h₀ 1 0 := by
      rw [div_mul_eq_mul_div, div_eq_iff hc₀]
      linear_combination A h 1 0 * hδ + (A h₀ 1 0 * δ) * hd - A h₀ 1 0 * hprop
    rw [happly, smul_add, smul_smul, smul_smul, e0, e1]

end TraceVanishingCoset

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "baseChange IsAbsolutelyIrreducible factorsThroughFiniteLevel finrank_eq V ρ mk isAbsolutelyIrreducible_iff_span_eq_top"
p2m_open "ResidualGaloisRep"

open scoped TensorProduct

private theorem false_of_index_eq_two_of_forall_notMem_trace_eq_zero {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (h2 : (2 : k) ≠ 0)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (Gs : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hGs : Gs.index = 2)
    {z : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hz : z ∉ Gs)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∉ Gs →
      LinearMap.trace k ρbar.V (ρbar.ρ σ) = 0) : False := by
  set K : Type := AlgebraicClosure k
  have h2K : (2 : K) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap k K).injective
    rw [map_ofNat, map_zero]
    exact h
  have htrK : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∉ Gs →
      LinearMap.trace K (ρbar.baseChange K).V ((ρbar.baseChange K).ρ σ) = 0 := by
    intro σ hσ
    show LinearMap.trace K (K ⊗[k] ρbar.V) ((ρbar.ρ σ).baseChange K) = 0
    rw [LinearMap.trace_baseChange, htr σ hσ, map_zero]
  obtain ⟨L, hLbot, hLtop, hL⟩ := TraceVanishingCoset.exists_submodule_ne_bot_ne_top_of_forall_notMem_trace_eq_zero
    (ρbar.baseChange K).finrank_eq h2K (ρbar.baseChange K).ρ Gs hz htrK
  rcases h3 K Gs hGs L hL with h | h
  · exact hLbot h
  · exact hLtop h

end ResidualGaloisRep

open Polynomial

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "baseChange IsAbsolutelyIrreducible factorsThroughFiniteLevel finrank_eq V ρ mk isAbsolutelyIrreducible_iff_span_eq_top"
p2m_open "ResidualGaloisRep"

namespace CubicTwist

section Plane

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]

private theorem exists_mul_self_eq_smul_one (hV : Module.finrank k V = 2) (f : Module.End k V)
    (hf : LinearMap.trace k V f = 0) : ∃ c : k, f * f = c • (1 : Module.End k V) := by
  haveI : Module.Finite k V := Module.finite_of_finrank_eq_succ hV
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hV
  rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace_fin_two] at hf
  set A := LinearMap.toMatrix b b f with hA
  refine ⟨-(A 0 0 * A 1 1 - A 0 1 * A 1 0), ?_⟩
  apply (LinearMap.toMatrix b b).injective
  rw [LinearMap.toMatrix_mul b, map_smul, LinearMap.toMatrix_one b, ← hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (A 0 0) * hf
  · linear_combination (A 0 1) * hf
  · linear_combination (A 1 0) * hf
  · linear_combination (A 1 1) * hf

private theorem trace_pow_eq_zero_of_odd (hV : Module.finrank k V = 2) (f : Module.End k V)
    (hf : LinearMap.trace k V f = 0) {n : ℕ} (hn : Odd n) : LinearMap.trace k V (f ^ n) = 0 := by
  obtain ⟨c, hc⟩ := exists_mul_self_eq_smul_one hV f hf
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, sq, hc, _root_.smul_pow, one_pow, smul_mul_assoc, one_mul, map_smul, hf, smul_zero]

end Plane

section CubeRoot

private theorem exists_isPrimitiveRoot_three : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ 3 := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic 3 (AlgebraicClosure ℚ))
    (degree_cyclotomic_pos 3 _ (by norm_num)).ne'
  exact ⟨ζ, isRoot_cyclotomic_iff.mp hζ⟩

variable {ζ : AlgebraicClosure ℚ}

private theorem pow_apply_eq_self (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ζ = ζ) (j : ℕ) :
    (σ ^ j) ζ = ζ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hσ, ih]

private theorem apply_eq_self_or_eq_sq (hζ : IsPrimitiveRoot ζ 3) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ζ = ζ ∨ σ ζ = ζ ^ 2 := by
  obtain ⟨i, hi, hiζ⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · rw [pow_zero] at hiζ
    exact absurd hiζ.symm ((hζ.map_of_injective σ.injective).ne_one (by norm_num))
  · exact Or.inl (by rw [← hiζ, pow_one])
  · exact Or.inr hiζ.symm

private theorem sq_ne_self (hζ : IsPrimitiveRoot ζ 3) : ζ ^ 2 ≠ ζ := fun h =>
  absurd (hζ.pow_inj (by norm_num) (by norm_num) (h.trans (pow_one ζ).symm)) (by norm_num)

private theorem orbit_eq (hζ : IsPrimitiveRoot ζ 3) :
    MulAction.orbit (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ = {ζ, ζ ^ 2} := by
  ext y
  constructor
  · rintro ⟨σ, rfl⟩
    show σ ζ ∈ ({ζ, ζ ^ 2} : Set (AlgebraicClosure ℚ))
    rcases apply_eq_self_or_eq_sq hζ σ with h | h
    · rw [h]; exact Set.mem_insert ζ _
    · rw [h]; exact Set.mem_insert_of_mem ζ (Set.mem_singleton _)
  · intro hy
    have key : ∀ y : AlgebraicClosure ℚ, IsPrimitiveRoot y 3 →
        y ∈ MulAction.orbit (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ := fun y hy =>
      (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := AlgebraicClosure ℚ)).mp
        (by rw [← cyclotomic_eq_minpoly_rat hy (by norm_num), ← cyclotomic_eq_minpoly_rat hζ (by norm_num)])
    rcases hy with h | h
    · rw [h]; exact MulAction.mem_orbit_self ζ
    · rw [Set.mem_singleton_iff] at h
      rw [h]; exact key _ (hζ.pow_of_coprime 2 (by norm_num))

private theorem index_stabilizer_eq_two (hζ : IsPrimitiveRoot ζ 3) :
    (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ).index = 2 := by
  rw [MulAction.index_stabilizer, orbit_eq hζ, Set.ncard_pair (sq_ne_self hζ).symm]

private theorem exists_notMem_stabilizer (hζ : IsPrimitiveRoot ζ 3) :
    ∃ z : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      z ∉ MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ := by
  by_contra hall
  push Not at hall
  have htop : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr hall
  have h := index_stabilizer_eq_two hζ
  rw [htop, Subgroup.index_top] at h
  exact absurd h (by norm_num)

end CubeRoot

section Transfer

variable {k : Type} [Field k]

private theorem trace_conj_eq (ρbar : ResidualGaloisRep k) (g τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.trace k ρbar.V (ρbar.ρ (g * τ * g⁻¹)) = LinearMap.trace k ρbar.V (ρbar.ρ τ) := by
  rw [ρbar.ρ.map_mul, ρbar.ρ.map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← ρbar.ρ.map_mul,
    inv_mul_cancel, ρbar.ρ.map_one, one_mul]

private theorem trace_eq_zero_of_apply_ne (N : ℕ) [NeZero N] (S : Finset ℕ) (ρbar : ResidualGaloisRep k)
    (htr0 : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N → ℓ % 3 = 2 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ τ) = 0)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 3)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ζ ≠ ζ) :
    LinearMap.trace k ρbar.V (ρbar.ρ σ) = 0 := by
  classical

  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI : FiniteDimensional ℚ L := hLfd
  have hζint : IsIntegral ℚ ζ :=
    IsIntegral.of_pow (by norm_num : 0 < 3) (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ} : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.adjoin.finiteDimensional hζint
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_sup L _
  have hFopen : IsOpen (F.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    IntermediateField.fixingSubgroup_isOpen F
  have hζF : ζ ∈ F :=
    (le_sup_right : IntermediateField.adjoin ℚ {ζ} ≤ F) (IntermediateField.subset_adjoin ℚ {ζ} rfl)
  have hρfix : ∀ u ∈ F.fixingSubgroup, ρbar.ρ u = 1 := fun u hu =>
    hL u fun x hx => (IntermediateField.mem_fixingSubgroup_iff F u).mp hu x ((le_sup_left : L ≤ F) hx)
  have hζfix : ∀ u ∈ F.fixingSubgroup, u ζ = ζ := fun u hu =>
    (IntermediateField.mem_fixingSubgroup_iff F u).mp hu ζ hζF

  have hM : 0 < 3 * N * (S.erase 0).prod id :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero (NeZero.ne N)))
      (Finset.prod_pos fun s hs => Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hs))

  obtain ⟨ℓ, A, τ, g, n, j, hℓ, hℓM, hA, hτ, hmem, -⟩ :=
    Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen F.fixingSubgroup hFopen σ hM
  have h3M : 3 ∣ 3 * N * (S.erase 0).prod id := dvd_mul_of_dvd_left (dvd_mul_right 3 N) _
  have hNM : N ∣ 3 * N * (S.erase 0).prod id := dvd_mul_of_dvd_left (dvd_mul_left N 3) _
  have hℓN : ¬ ℓ ∣ N := fun h => hℓM (h.trans hNM)
  have hℓS : ℓ ∉ S := fun hS => hℓM (dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem id (Finset.mem_erase.mpr ⟨hℓ.ne_zero, hS⟩)) (3 * N))
  have h3ℓ : ¬ 3 ∣ ℓ := fun h =>
    hℓM (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).mp h) ▸ h3M)
  have hcop : Nat.Coprime 3 ℓ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3ℓ

  have hτu : τ (g⁻¹ ζ) = (g⁻¹ ζ) ^ ℓ :=
    ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ ℓ 3 hA hτ hcop (g⁻¹ ζ)
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hτ'ζ : (g * τ * g⁻¹) ζ = ζ ^ ℓ := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτu, map_pow, ← AlgEquiv.mul_apply, mul_inv_cancel,
      AlgEquiv.one_apply]

  have hconj : g * τ ^ n * g⁻¹ = (g * τ ^ n * g⁻¹ * σ⁻¹) * σ := by group
  have hmove : ((g * τ * g⁻¹) ^ n) ζ ≠ ζ := by
    intro h
    rw [conj_pow, hconj, AlgEquiv.mul_apply] at h
    apply hσ
    calc σ ζ = ((g * τ ^ n * g⁻¹ * σ⁻¹)⁻¹ * (g * τ ^ n * g⁻¹ * σ⁻¹)) (σ ζ) := by
          rw [inv_mul_cancel, AlgEquiv.one_apply]
      _ = (g * τ ^ n * g⁻¹ * σ⁻¹)⁻¹ ζ := by rw [AlgEquiv.mul_apply, h]
      _ = ζ := hζfix _ (F.fixingSubgroup.inv_mem hmem)
  have hτ'ne : (g * τ * g⁻¹) ζ ≠ ζ := fun h => hmove (pow_apply_eq_self _ h n)

  have hℓmod : ℓ % 3 = 2 := by
    have h0 : ℓ % 3 ≠ 0 := fun h => h3ℓ (Nat.dvd_of_mod_eq_zero h)
    have h1 : ℓ % 3 ≠ 1 := fun h => hτ'ne (by
      rw [hτ'ζ, ← Nat.div_add_mod ℓ 3, h, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul])
    have h2 : ℓ % 3 < 3 := Nat.mod_lt ℓ (by norm_num)
    omega

  have hτ'sq : (g * τ * g⁻¹) ζ = ζ ^ 2 := (apply_eq_self_or_eq_sq hζ _).resolve_left hτ'ne
  have hodd : Odd n := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ho
    · exfalso
      apply hmove
      have hsq : ((g * τ * g⁻¹) ^ 2) ζ = ζ := by
        rw [pow_two, AlgEquiv.mul_apply, hτ'sq, map_pow, hτ'sq, ← pow_mul,
          show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, hζ.pow_eq_one, one_mul]
      rw [hm, ← two_mul, pow_mul]
      exact pow_apply_eq_self _ hsq m
    · exact ho

  have hτtr : LinearMap.trace k ρbar.V (ρbar.ρ (g * τ * g⁻¹)) = 0 := by
    rw [trace_conj_eq]
    exact htr0 ℓ hℓ hℓS hℓN hℓmod A hA τ hτ
  have hσeq : ρbar.ρ σ = ρbar.ρ (g * τ * g⁻¹) ^ n := by
    rw [← map_pow, conj_pow, hconj, map_mul, hρfix _ hmem, one_mul]
  rw [hσeq]
  exact trace_pow_eq_zero_of_odd ρbar.finrank_eq _ hτtr hodd

end Transfer

end CubicTwist

private theorem false_of_forall_trace_frobenius_eq_zero_of_modEq_two (N : ℕ) [NeZero N] (S : Finset ℕ)
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (htr0 : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N → ℓ % 3 = 2 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ τ) = 0) : False := by
  obtain ⟨ζ, hζ⟩ := CubicTwist.exists_isPrimitiveRoot_three
  obtain ⟨z, hz⟩ := CubicTwist.exists_notMem_stabilizer hζ
  have h2 : (2 : k) ≠ 0 := fun h => by
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    have h'' := (CharP.cast_eq_zero_iff k 3 2).mp h'
    omega
  exact false_of_index_eq_two_of_forall_notMem_trace_eq_zero ρbar h2 h3
    (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ)
    (CubicTwist.index_stabilizer_eq_two hζ) hz
    fun σ hσ => CubicTwist.trace_eq_zero_of_apply_ne N S ρbar htr0 hζ σ
      (by rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hσ)

end ResidualGaloisRep

end PieceSliceThree

section PieceEllipticLift

namespace EllipticLift

open scoped MatrixGroups
open CongruenceSubgroup Matrix.SpecialLinearGroup

private theorem zmod_three_eq_zero_of_add_self (x : ZMod 3) (h : x + x = 0) : x = 0 := by
  revert x
  decide

private theorem sq_eq_neg_one_of_trace (γ : SL(2, ℤ)) (ht : (γ : Matrix (Fin 2) (Fin 2) ℤ).trace = 0) : γ ^ 2 = -1 := by
  apply Subtype.ext
  rw [coe_pow, pow_two, EllipticTransfer.coe_mul_self_eq, ht, zero_smul, zero_sub, coe_neg, coe_one]

private theorem apply_eq_zero_of_coe_eq_neg_one {N : ℕ} (w : CohCarrier.H1 N ⊤ (ZMod 3))
    (γ : ↥(CohCarrier.GammaH N ⊤)) (hγ : (γ : SL(2, ℤ)) = -1) : w (Additive.ofMul γ) = 0 := by
  apply zmod_three_eq_zero_of_add_self
  have hγ2 : γ * γ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hγ, neg_mul_neg, one_mul, OneMemClass.coe_one]
  rw [← map_add, ← ofMul_mul, hγ2, ofMul_one, map_zero]

private theorem apply_eq_zero_of_sq_eq_neg_one {N : ℕ} (w : CohCarrier.H1 N ⊤ (ZMod 3))
    (γ : ↥(CohCarrier.GammaH N ⊤)) (hγ : (γ : SL(2, ℤ)) ^ 2 = -1) : w (Additive.ofMul γ) = 0 := by
  apply zmod_three_eq_zero_of_add_self
  have h2 : w (Additive.ofMul (γ ^ 2)) = 0 :=
    apply_eq_zero_of_coe_eq_neg_one w (γ ^ 2) (by rw [SubgroupClass.coe_pow, hγ])
  rwa [pow_two, ofMul_mul, map_add] at h2

private theorem apply_eq_zero_of_isOfFinOrder (N : ℕ) [NeZero N] (S : Finset ℕ) (n : ℕ → ℤ)
    (w : CohCarrier.H1 N ⊤ (ZMod 3))
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊤ ℓ (ZMod 3) w = n ℓ • w)
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (htr : ∀ (ℓ : ℕ) (_ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k))
    (γ : ↥(CohCarrier.GammaH N ⊤)) (hγ : IsOfFinOrder γ) : w (Additive.ofMul γ) = 0 := by
  have hγ' : IsOfFinOrder (γ : SL(2, ℤ)) := (CohCarrier.GammaH N ⊤).subtype.isOfFinOrder hγ
  rcases TraceOfFiniteOrder.trace_mem_of_isOfFinOrder _ hγ' with ht | ht | ht | ht | ht
  · exact apply_eq_zero_of_coe_eq_neg_one w γ
      (TraceOfFiniteOrder.eq_neg_one_of_isOfFinOrder_of_trace_eq_neg_two _ hγ' ht)
  rotate_left
  · exact apply_eq_zero_of_sq_eq_neg_one w γ (sq_eq_neg_one_of_trace _ ht)
  rotate_left
  · have h1 : γ = 1 :=
      Subtype.ext (TraceOfFiniteOrder.eq_one_of_isOfFinOrder_of_trace_eq_two _ hγ' ht)
    rw [h1, ofMul_one, map_zero]

  all_goals
    have htr' : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 ∨
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = -1 := by simp [ht]
    have hF : w (Additive.ofMul (γ ^ 3)) = 0 := by
      rcases EllipticTransfer.cube_eq_of_trace _ htr' with hc | hc
      · have h1 : γ ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hc, OneMemClass.coe_one])
        rw [h1, ofMul_one, map_zero]
      · exact apply_eq_zero_of_coe_eq_neg_one w (γ ^ 3) (by rw [SubgroupClass.coe_pow, hc])
    by_contra hne0
    refine ResidualGaloisRep.false_of_forall_trace_frobenius_eq_zero_of_modEq_two N S k ρbar h3 ?_
    intro ℓ hℓ hℓS hℓN hℓ3 A hA τ hτ
    rw [htr ℓ hℓ hℓS hℓN A hA τ hτ]
    haveI := Fact.mk hℓ
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hE := EllipticTransfer.heckeT_apply_eq_zero_of_trace N ℓ hℓ3 w γ htr' hF
    have hT' : CohCarrier.heckeT N ⊤ ℓ (ZMod 3) w (Additive.ofMul γ) = n ℓ • w (Additive.ofMul γ) := by
      rw [hT ℓ hℓ hℓS hℓN]
      rfl
    have hz : n ℓ • w (Additive.ofMul γ) = 0 := hT'.symm.trans hE
    rw [zsmul_eq_mul] at hz
    have h0 : ((n ℓ : ℤ) : ZMod 3) = 0 := (mul_eq_zero.mp hz).resolve_right hne0
    exact (CharP.intCast_eq_zero_iff k 3 (n ℓ)).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0)

private theorem exists_castAddHom_comp_eq_of_three (N : ℕ) [NeZero N] (S : Finset ℕ) (n : ℕ → ℤ)
    (w : CohCarrier.H1 N ⊤ (ZMod 3))
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N ⊤ ℓ (ZMod 3) w = n ℓ • w)
    {ℓ₀ : ℕ} (hℓ₀ : ℓ₀.Prime) (hℓ₀S : ℓ₀ ∉ S) (hℓ₀N : ¬ ℓ₀ ∣ N)
    (hℓ₀1 : ∀ t : ℕ, t * t ∣ N → ℓ₀ ≡ 1 [MOD t]) (hne : ¬ (3 : ℤ) ∣ n ℓ₀ - (ℓ₀ + 1 : ℕ))
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (htr : ∀ (ℓ : ℕ) (_ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k)) :
    ∃ φ : CohCarrier.H1 N ⊤ ℤ, (Int.castAddHom (ZMod 3)).comp φ = w := by

  have hpar : w ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊤) (ZMod 3) := by
    haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩
    have hb := CohCarrier.heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one N (ZMod 3) w ℓ₀ hℓ₀
      hℓ₀N hℓ₀1
    rw [hT ℓ₀ hℓ₀ hℓ₀S hℓ₀N, ← natCast_zsmul, ← sub_smul] at hb
    obtain ⟨u, v, huv⟩ := (Prime.coprime_iff_not_dvd Int.prime_three).mpr hne
    have h3w : (3 : ℤ) • w = 0 := by
      ext x
      show (3 : ℤ) • w x = 0
      rw [zsmul_eq_mul]
      have h30 : ((3 : ℤ) : ZMod 3) = 0 := by decide
      rw [h30, zero_mul]
    have hw : w = v • ((n ℓ₀ - (ℓ₀ + 1 : ℕ)) • w) := by
      conv_lhs => rw [← one_smul ℤ w, ← huv]
      rw [add_smul, mul_smul, h3w, smul_zero, zero_add, mul_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hb
  have hpar' : w ∈ ModularCurve.Period.parabolicHoms (ZMod 3) (CohCarrier.GammaH N ⊤) (ZMod 3) :=
    ModularCurve.Period.mem_parabolicHoms_iff.mpr (ModularCurve.Period.mem_parabolicHoms_iff.mp hpar)

  haveI : (CohCarrier.GammaH N ⊤).FiniteIndex := by
    rw [CohCarrier.GammaH_top]
    infer_instance
  obtain ⟨x, hx⟩ :=
    ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder
      (CohCarrier.GammaH N ⊤) 3 ⟨w, hpar'⟩
      (fun γ hγ => apply_eq_zero_of_isOfFinOrder N S n w hT k ρbar h3 htr γ hγ)
  exact ⟨x, hx⟩

end EllipticLift

end PieceEllipticLift

section PieceLift5

p2m_open "CategoryTheory groupCohomology CohCarrier P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible.CohCarrier CongruenceSubgroup"

namespace IntegralLift

section Abstract

variable {k : Type} [CommRing k] {G : Type} [Group G]

section SES

variable (G) (a : k) {Q : Type} [AddCommGroup Q] [Module k Q] (red : k →ₗ[k] Q)

private noncomputable def mulHom : Rep.trivial k G k ⟶ Rep.trivial k G k :=
  Rep.ofHom ((LinearMap.mulLeft k a).intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl))

private noncomputable def redHom : Rep.trivial k G k ⟶ Rep.trivial k G Q :=
  Rep.ofHom (red.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl))

private noncomputable abbrev ses (h0 : ∀ x : k, red (a * x) = 0) : ShortComplex (Rep k G) where
  X₁ := Rep.trivial k G k
  X₂ := Rep.trivial k G k
  X₃ := Rep.trivial k G Q
  f := mulHom G a
  g := redHom G red
  zero := by
    ext
    simpa [mulHom, redHom] using h0 1

private theorem ses_shortExact (h0 : ∀ x : k, red (a * x) = 0) (ha : ∀ x : k, a * x = 0 → x = 0) (hsurj : Function.Surjective red)
    (hex : ∀ x : k, red x = 0 → ∃ y : k, x = a * y) : (ses G a red h0).ShortExact where
  exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
      have hx' : red x = 0 := hx
      obtain ⟨y, hy⟩ := hex x hx'
      refine ⟨y, ?_⟩
      change a * y = x
      exact hy.symm
  mono_f := (Rep.mono_iff_injective _).2 (by
    change Function.Injective (fun x : k => a * x)
    intro x y hxy
    have h : a * (x - y) = 0 := by
      rw [mul_sub, sub_eq_zero]
      exact hxy
    exact sub_eq_zero.1 (ha _ h))
  epi_g := (Rep.epi_iff_surjective _).2 (by
    change Function.Surjective (fun x : k => red x)
    exact hsurj)

end SES

private theorem exists_lift (h2 : Subsingleton (groupCohomology (Rep.trivial k G k) 2))
    (a : k) {Q : Type} [AddCommGroup Q] [Module k Q] (red : k →ₗ[k] Q)
    (h0 : ∀ x : k, red (a * x) = 0) (ha : ∀ x : k, a * x = 0 → x = 0)
    (hsurj : Function.Surjective red) (hex : ∀ x : k, red x = 0 → ∃ y : k, x = a * y)
    (w : Additive G →+ Q) : ∃ φ : Additive G →+ k, ∀ g : Additive G, red (φ g) = w g := by
  have hX := ses_shortExact G a red h0 ha hsurj hex
  have hexact := mapShortComplex₃_exact hX (i := 1) (j := 2) rfl
  have hg0 : (mapShortComplex₃ hX (i := 1) (j := 2) rfl).g = 0 := by
    have hz : Limits.IsZero (mapShortComplex₃ hX (i := 1) (j := 2) rfl).X₃ := by
      change Limits.IsZero (groupCohomology (Rep.trivial k G k) 2)
      haveI := h2
      exact ModuleCat.isZero_of_subsingleton _
    exact hz.eq_zero_of_tgt _
  have hepi : Epi (mapShortComplex₃ hX (i := 1) (j := 2) rfl).f := hexact.epi_f hg0
  have hf : (mapShortComplex₃ hX (i := 1) (j := 2) rfl).f = map (MonoidHom.id G) (ses G a red h0).g 1 :=
    rfl
  rw [hf] at hepi
  have hsurjH := (ModuleCat.epi_iff_surjective _).1 hepi
  set cw : cocycles₁ (Rep.trivial k G Q) := (cocycles₁IsoOfIsTrivial (Rep.trivial k G Q)).inv w
  obtain ⟨c, hc⟩ := hsurjH (H1π (Rep.trivial k G Q) cw)
  induction c using H1_induction_on with
  | h f =>
    refine ⟨(cocycles₁IsoOfIsTrivial (Rep.trivial k G k)).hom f, fun g => ?_⟩
    have h1 := H1π_comp_map_apply (A := (ses G a red h0).X₂) (B := (ses G a red h0).X₃)
      (f := MonoidHom.id G) (φ := (ses G a red h0).g) f
    have hc' : H1π (Rep.trivial k G Q) (mapCocycles₁ (MonoidHom.id G) (ses G a red h0).g f)
        = H1π (Rep.trivial k G Q) cw := h1.symm.trans hc
    have hcob := (H1π_eq_iff _ _).1 hc'
    rw [coboundaries₁_eq_bot_of_isTrivial, Submodule.mem_bot, sub_eq_zero] at hcob
    have hval := congrFun hcob (Additive.toMul g)
    have hw : (cw : G → Q) (Additive.toMul g) = w g := rfl
    have hL : (mapCocycles₁ (MonoidHom.id G) (ses G a red h0).g f : G → Q) (Additive.toMul g)
        = red (f (Additive.toMul g)) := rfl
    rw [hL, hw] at hval
    first | exact hval | simpa using hval | (rw [hL]; exact hval)

private theorem exists_comp_eq {X A B : Type} [AddGroup X] [AddCommGroup A] [AddCommGroup B]
    (m : A →+ B) (hm : Function.Injective m) (θ : X →+ B) (h : ∀ x, ∃ y, m y = θ x) :
    ∃ ψ : X →+ A, m.comp ψ = θ := by
  choose ψ hψ using h
  refine ⟨AddMonoidHom.mk' ψ fun x y => hm ?_, ?_⟩
  · rw [map_add, hψ, hψ, hψ, map_add]
  · ext x
    exact hψ x

end Abstract

section Coefficients

private abbrev R6 : Type := Localization.Away (6 : ℤ)

private theorem six_ne_zero' : (6 : ℤ) ≠ 0 := by norm_num

private theorem algebraMap_injective : Function.Injective (algebraMap ℤ R6) :=
  IsLocalization.injective (M := Submonoid.powers (6 : ℤ)) R6
    (powers_le_nonZeroDivisors_of_noZeroDivisors six_ne_zero')

private theorem isUnit_six : IsUnit (6 : R6) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := R6) (6 : ℤ)
  rwa [map_ofNat] at h

private theorem exists_pow_mul_eq (x : R6) : ∃ (j : ℕ) (z : ℤ), x * (6 : R6) ^ j = algebraMap ℤ R6 z := by
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (6 : ℤ)) x
  obtain ⟨j, hj⟩ := s.2
  refine ⟨j, z, ?_⟩
  have h6 : (6 : R6) ^ j = algebraMap ℤ R6 (s : ℤ) := by
    rw [← hj]
    simp
  rw [h6]
  exact hs

variable (p : ℕ) [hp : Fact p.Prime]

private theorem p_mul_eq_zero (x : R6) (h : (p : R6) * x = 0) : x = 0 := by
  have hp0 : (p : R6) ≠ 0 := by
    intro h0
    have h0' : algebraMap ℤ R6 (p : ℤ) = algebraMap ℤ R6 0 := by simpa using h0
    have h1 : (p : ℤ) = 0 := algebraMap_injective h0'
    exact hp.out.ne_zero (by exact_mod_cast h1)
  exact (mul_eq_zero.1 h).resolve_left hp0

variable (hp2 : p ≠ 2) (hp3 : p ≠ 3)
include hp2 hp3

private theorem not_p_dvd_six : ¬ p ∣ 6 := by
  intro h
  rcases (Nat.Prime.dvd_mul hp.out).1 (show p ∣ 2 * 3 from h) with h2 | h3
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2)
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h3)

private theorem coprime_six_p : Nat.Coprime 6 p :=
  ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (not_p_dvd_six p hp2 hp3)).symm

private theorem isUnit_six_zmod : IsUnit ((6 : ℕ) : ZMod p) :=
  (ZMod.isUnit_iff_coprime 6 p).2 (coprime_six_p p hp2 hp3)

private noncomputable def red : R6 →+* ZMod p :=
  IsLocalization.Away.lift (6 : ℤ) (g := Int.castRingHom (ZMod p)) (by
    have h := isUnit_six_zmod p hp2 hp3
    simpa using h)

private theorem red_algebraMap (z : ℤ) : red p hp2 hp3 (algebraMap ℤ R6 z) = (z : ZMod p) :=
  IsLocalization.Away.lift_eq _ _ _

private theorem redMap_surjective : Function.Surjective (red p hp2 hp3) := fun q => by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective q
  exact ⟨algebraMap ℤ R6 z, red_algebraMap p hp2 hp3 z⟩

private theorem red_p_mul (x : R6) : red p hp2 hp3 ((p : R6) * x) = 0 := by
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

private theorem red_eq_zero_imp (x : R6) (hx : red p hp2 hp3 x = 0) : ∃ y : R6, x = (p : R6) * y := by
  obtain ⟨j, z, hz⟩ := exists_pow_mul_eq x
  have hu : IsUnit ((6 : R6) ^ j) := isUnit_six.pow j
  have hred : (z : ZMod p) = 0 := by
    rw [← red_algebraMap p hp2 hp3, ← hz, map_mul, hx, zero_mul]
  obtain ⟨b, hb⟩ : (p : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 hred
  refine ⟨algebraMap ℤ R6 b * ↑(hu.unit⁻¹), ?_⟩
  have hx' : x = algebraMap ℤ R6 z * ↑(hu.unit⁻¹) := by
    rw [← hz, mul_assoc]
    have : (6 : R6) ^ j * ↑(hu.unit⁻¹) = 1 := hu.mul_val_inv
    rw [this, mul_one]
  rw [hx', hb]
  simp only [map_mul, map_natCast]
  ring

end Coefficients

section Level

variable (N : ℕ) [NeZero N]

private noncomputable def e : ↥(GammaH N ⊤) ≃* ↥(Gamma0 N) := MulEquiv.subgroupCongr GammaH_top

private scoped instance fg_sl2z : Group.FG (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
  Group.fg_iff.2 ⟨{ModularGroup.S, ModularGroup.T}, _root_.SpecialLinearGroup.SL2Z_generators,
    Set.toFinite _⟩

private scoped instance finiteIndex_gammaH_top : (GammaH N ⊤).FiniteIndex := by
  rw [GammaH_top]
  infer_instance

private scoped instance fg_gammaH_top : Group.FG ↥(GammaH N ⊤) := inferInstance

private theorem exists_pow_six_smul_eq (φ : H1 N ⊤ R6) :
    ∃ (m : ℕ) (x : H1 N ⊤ ℤ), (algebraMap ℤ R6).toAddMonoidHom.comp x = (6 : R6) ^ m • φ := by
  obtain ⟨T, hTtop, hTfin⟩ := Group.fg_iff.1 (fg_gammaH_top N)

  choose j z hjz using fun t : ↥(GammaH N ⊤) => exists_pow_mul_eq (φ (Additive.ofMul t))
  let m : ℕ := hTfin.toFinset.sup j

  let K : Subgroup ↥(GammaH N ⊤) :=
    { carrier := {t | ∃ a : ℤ, algebraMap ℤ R6 a = (6 : R6) ^ m * φ (Additive.ofMul t)}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := by
        rintro s t ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        rw [map_add, ha, hb, ofMul_mul, map_add, mul_add]
      inv_mem' := by
        rintro t ⟨a, ha⟩
        refine ⟨-a, ?_⟩
        rw [map_neg, ha, ofMul_inv, map_neg]
        ring }
  have hTK : T ⊆ K := by
    intro t ht
    have hjm : j t ≤ m := Finset.le_sup (f := j) (hTfin.mem_toFinset.2 ht)
    refine ⟨z t * 6 ^ (m - j t), ?_⟩
    rw [map_mul, ← hjz t, map_pow, map_ofNat, mul_assoc, ← pow_add, Nat.add_sub_of_le hjm, mul_comm]
  have hK : ∀ t, t ∈ K := by
    intro t
    have : (⊤ : Subgroup ↥(GammaH N ⊤)) ≤ K := hTtop ▸ (Subgroup.closure_le K).2 hTK
    exact this (Subgroup.mem_top t)
  have hvals : ∀ t : Additive ↥(GammaH N ⊤),
      ∃ a : ℤ, (algebraMap ℤ R6).toAddMonoidHom a = ((6 : R6) ^ m • φ) t := by
    intro t
    obtain ⟨a, ha⟩ := hK (Additive.toMul t)
    exact ⟨a, by simpa using ha⟩
  obtain ⟨x, hx⟩ := exists_comp_eq (algebraMap ℤ R6).toAddMonoidHom algebraMap_injective
    ((6 : R6) ^ m • φ) hvals
  exact ⟨m, x, hx⟩

omit [NeZero N] in

private theorem exists_lift_gamma0 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (w : Additive ↥(Gamma0 N) →+ ZMod p) :
    ∃ φ : Additive ↥(Gamma0 N) →+ R6, ∀ g, red p hp2 hp3 (φ g) = w g := by
  letI : Algebra R6 (ZMod p) := (red p hp2 hp3).toAlgebra
  have h2 : Subsingleton (groupCohomology (Rep.trivial R6 ↥(Gamma0 N) R6) 2) :=
    TW12CD1Dock.subsingleton_H2_gamma0 N isUnit_six _
  obtain ⟨φ, hφ⟩ := exists_lift h2 (p : R6) (Algebra.linearMap R6 (ZMod p))
    (fun x => red_p_mul p hp2 hp3 x) (p_mul_eq_zero p) (redMap_surjective p hp2 hp3)
    (fun x hx => red_eq_zero_imp p hp2 hp3 x hx) w
  exact ⟨φ, hφ⟩

private theorem exists_castAddHom_comp_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (w : H1 N ⊤ (ZMod p)) : ∃ φ : H1 N ⊤ ℤ, (Int.castAddHom (ZMod p)).comp φ = w := by

  set e' := e N
  obtain ⟨φ₀, hφ₀⟩ := exists_lift_gamma0 N p hp2 hp3
    (w.comp (MonoidHom.toAdditive e'.symm.toMonoidHom))
  let φ' : H1 N ⊤ R6 := φ₀.comp (MonoidHom.toAdditive e'.toMonoidHom)
  have hw' : ∀ g, red p hp2 hp3 (φ' g) = w g := fun g => by
    simp [φ', hφ₀]

  obtain ⟨m, φ₁, hφ₁⟩ := exists_pow_six_smul_eq N φ'
  have hφ₁' : ∀ g, algebraMap ℤ R6 (φ₁ g) = (6 : R6) ^ m * φ' g := fun g => by
    have h := congrArg (fun χ : H1 N ⊤ R6 => χ g) hφ₁
    simpa using h
  have hred6 : red p hp2 hp3 ((6 : R6) ^ m) = ((6 : ℕ) : ZMod p) ^ m := by
    rw [map_pow]
    congr 1
    rw [show (6 : R6) = algebraMap ℤ R6 6 by simp, red_algebraMap]
    simp
  have hφ₁w : ∀ g, ((φ₁ g : ℤ) : ZMod p) = ((6 : ℕ) : ZMod p) ^ m * w g := fun g => by
    rw [← red_algebraMap p hp2 hp3, hφ₁' g, map_mul, hred6, hw' g]

  have h6 : IsUnit (((6 : ℕ) : ZMod p) ^ m) := (isUnit_six_zmod p hp2 hp3).pow m
  obtain ⟨u, hu⟩ := ZMod.intCast_surjective (↑h6.unit⁻¹ : ZMod p)
  have hu6 : (u : ZMod p) * ((6 : ℕ) : ZMod p) ^ m = 1 := by
    rw [hu]
    exact h6.val_inv_mul
  refine ⟨u • φ₁, AddMonoidHom.ext fun g => ?_⟩
  rw [AddMonoidHom.comp_apply, Int.coe_castAddHom]
  have hg : (u • φ₁) g = u * φ₁ g := by simp
  rw [hg]
  show ((u * φ₁ g : ℤ) : ZMod p) = w g
  rw [Int.cast_mul, hφ₁w g, ← mul_assoc, hu6, one_mul]

end Level

end IntegralLift
p2m_reactivate "P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible.IntegralLift"

end PieceLift5
p2m_reactivate "P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible.IntegralLift"

section PieceGoingUp

namespace CohCarrierGoingUp

section Core

variable {R : Type} [CommRing R] {L : Type} [AddCommGroup L] (ρ : R →+* Module.End ℤ L)

private def carryIdeal (p : ℕ) (φ : L) : Ideal R where
  carrier := {t | ∃ ψ : L, ρ t φ = p • ψ}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro s t ⟨ψs, hs⟩ ⟨ψt, ht⟩
    exact ⟨ψs + ψt, by rw [map_add, LinearMap.add_apply, hs, ht, smul_add]⟩
  smul_mem' := by
    rintro a t ⟨ψ, hψ⟩
    exact ⟨ρ a ψ, by rw [smul_eq_mul, map_mul, Module.End.mul_apply, hψ, map_nsmul]⟩

private theorem mem_carryIdeal_iff {p : ℕ} {φ : L} {t : R} :
    t ∈ carryIdeal ρ p φ ↔ ∃ ψ : L, ρ t φ = p • ψ :=
  Iff.rfl

private theorem natCast_mem_carryIdeal (p : ℕ) (φ : L) : (p : R) ∈ carryIdeal ρ p φ :=
  ⟨φ, by rw [map_natCast, Module.End.natCast_apply]⟩

private theorem sub_intCast_mem_carryIdeal {p : ℕ} {φ : L} {t : R} {n : ℤ}
    (h : ∃ ψ : L, ρ t φ - n • φ = p • ψ) : t - (n : R) ∈ carryIdeal ρ p φ := by
  obtain ⟨ψ, hψ⟩ := h
  exact ⟨ψ, by rw [map_sub, LinearMap.sub_apply, map_intCast, Module.End.intCast_apply, hψ]⟩

private theorem carryIdeal_ne_top {p : ℕ} {φ : L} (hφ : ¬ ∃ ψ : L, φ = p • ψ) :
    carryIdeal ρ p φ ≠ ⊤ := by
  intro htop
  have h1 : (1 : R) ∈ carryIdeal ρ p φ := htop ▸ Submodule.mem_top
  obtain ⟨ψ, hψ⟩ := (mem_carryIdeal_iff ρ).mp h1
  rw [map_one, Module.End.one_apply] at hψ
  exact hφ ⟨ψ, hψ⟩

private theorem exists_isMaximal_of_forall_mem_carryIdeal {p : ℕ} {φ : L} (hφ : ¬ ∃ ψ : L, φ = p • ψ)
    (gens : Set R) (hgens : ∀ t ∈ gens, t ∈ carryIdeal ρ p φ) :
    ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ (p : R) ∈ 𝔪 ∧ ∀ t ∈ gens, t ∈ 𝔪 := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ (carryIdeal_ne_top ρ hφ)
  exact ⟨𝔪, h𝔪, hle (natCast_mem_carryIdeal ρ p φ), fun t ht => hle (hgens t ht)⟩

end Core
p2m_reactivate "P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible.IntegralLift"

section HeckeAlgebra

open ModularCurve.Period

private theorem mem_parabolicHoms_of_smul_mem {N : ℕ} {p : ℕ} (hp : p ≠ 0) {H : Subgroup (ZMod N)ˣ}
    {ψ : CohCarrier.H1 N H ℤ}
    (h : (p : ℤ) • ψ ∈ parabolicHoms ℤ (CohCarrier.GammaH N H) ℤ) : ψ ∈ parabolicHoms ℤ (CohCarrier.GammaH N H) ℤ := by
  rw [mem_parabolicHoms_iff] at h ⊢
  intro γ hγ
  have hγ' : (p : ℤ) * ψ (Additive.ofMul γ) = 0 := by simpa using h γ hγ
  rcases mul_eq_zero.mp hγ' with hp0 | hψ
  · exact absurd (by exact_mod_cast hp0) hp
  · exact hψ

variable (N : ℕ) [NeZero N]

private theorem exists_isMaximal_heckeAlgebra_of_top (p : ℕ) (hp : p ≠ 0) (S₀ : Set ℕ) (S : Finset ℕ) (n : ℕ → ℤ)
    (φ : CohCarrier.H1 N ⊤ ℤ) (hφpar : φ ∈ parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ)
    (hφ : ¬ ∃ ψ : CohCarrier.H1 N ⊤ ℤ, φ = (p : ℤ) • ψ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ ψ : CohCarrier.H1 N ⊤ ℤ, CohCarrier.heckeT N ⊤ ℓ ℤ φ - n ℓ • φ = (p : ℤ) • ψ) :
    ∃ 𝔪 : Ideal (CuspForm.heckeAlgebra N 2 S₀), 𝔪.IsMaximal ∧
      (p : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₀ : ℓ ∉ S₀), ℓ ∉ S →
        CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀ - (n ℓ : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪 := by
  obtain ⟨-, ρ, -, hρT, -⟩ := CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms N S₀
  let φL : ↥(parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ) := ⟨φ, hφpar⟩

  have hφL : ¬ ∃ ψ : ↥(parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ), φL = p • ψ := by
    rintro ⟨ψ, hψ⟩
    refine hφ ⟨(ψ : CohCarrier.H1 N ⊤ ℤ), ?_⟩
    have h := congrArg Subtype.val hψ
    simpa using h

  let gens : Set (CuspForm.heckeAlgebra N 2 S₀) :=
    {t | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₀ : ℓ ∉ S₀), ℓ ∉ S ∧
      t = CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀ - (n ℓ : CuspForm.heckeAlgebra N 2 S₀)}
  have hgens : ∀ t ∈ gens, t ∈ carryIdeal ρ p φL := by
    rintro t ⟨ℓ, hℓ, hℓN, hℓS₀, hℓS, rfl⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨ψ, hψ⟩ := hT ℓ hℓ hℓS hℓN

    have h1 := hρT ℓ hℓ hℓN hℓS₀ φL
    have hTφ : CohCarrier.heckeT N ⊤ ℓ ℤ φ ∈ parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ := by
      rw [← h1]
      exact (ρ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀) φL).2
    have hψL : ψ ∈ parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ := by
      have hmem : CohCarrier.heckeT N ⊤ ℓ ℤ φ - n ℓ • φ ∈ parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ :=
        Submodule.sub_mem _ hTφ (Submodule.smul_mem _ (n ℓ) hφpar)
      rw [hψ] at hmem
      exact mem_parabolicHoms_of_smul_mem hp hmem
    refine sub_intCast_mem_carryIdeal ρ ⟨⟨ψ, hψL⟩, ?_⟩
    apply Subtype.ext
    have h2 : CohCarrier.heckeT N ⊤ ℓ ℤ φ - n ℓ • φ = p • ψ := by simpa using hψ
    show ((ρ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀) φL : ↥(parabolicHoms ℤ (CohCarrier.GammaH N ⊤) ℤ)) :
        CohCarrier.H1 N ⊤ ℤ) - n ℓ • φ = p • ψ
    rw [h1]
    exact h2
  obtain ⟨𝔪, h𝔪, hp𝔪, hgens𝔪⟩ := exists_isMaximal_of_forall_mem_carryIdeal ρ hφL gens hgens
  exact ⟨𝔪, h𝔪, hp𝔪, fun ℓ hℓ hℓN hℓS₀ hℓS => hgens𝔪 _ ⟨ℓ, hℓ, hℓN, hℓS₀, hℓS, rfl⟩⟩

private theorem exists_isMaximal_heckeAlgebra_of_top_of_witness (p : ℕ) (hp : p.Prime) (S₀ : Set ℕ) (S : Finset ℕ)
    (n : ℕ → ℤ) (φ : CohCarrier.H1 N ⊤ ℤ)
    (hφ : ¬ ∃ ψ : CohCarrier.H1 N ⊤ ℤ, φ = (p : ℤ) • ψ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ ψ : CohCarrier.H1 N ⊤ ℤ, CohCarrier.heckeT N ⊤ ℓ ℤ φ - n ℓ • φ = (p : ℤ) • ψ)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀.Prime) (hℓ₀S : ℓ₀ ∉ S) (hℓ₀N : ¬ ℓ₀ ∣ N)
    (hℓ₀sq : ∀ t : ℕ, t * t ∣ N → ℓ₀ ≡ 1 [MOD t])
    (hnoneis : ¬ (p : ℤ) ∣ n ℓ₀ - (ℓ₀ + 1 : ℕ)) :
    ∃ 𝔪 : Ideal (CuspForm.heckeAlgebra N 2 S₀), 𝔪.IsMaximal ∧
      (p : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₀ : ℓ ∉ S₀), ℓ ∉ S →
        CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀ - (n ℓ : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪 := by
  haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩

  set φ' : CohCarrier.H1 N ⊤ ℤ := CohCarrier.heckeT N ⊤ ℓ₀ ℤ φ - (ℓ₀ + 1) • φ with hφ'def
  obtain ⟨ψ₀, hψ₀⟩ := hT ℓ₀ hℓ₀ hℓ₀S hℓ₀N

  have hφ'eq : φ' = (n ℓ₀ - (ℓ₀ + 1 : ℕ)) • φ + (p : ℤ) • ψ₀ := by
    rw [hφ'def, ← hψ₀, sub_smul, natCast_zsmul]
    abel
  refine exists_isMaximal_heckeAlgebra_of_top N p hp.ne_zero S₀ S n φ'
    (CohCarrier.heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one N ℤ φ ℓ₀ hℓ₀ hℓ₀N hℓ₀sq) ?_ ?_
  ·
    rintro ⟨χ, hχ⟩
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpZ).mpr hnoneis

    apply hφ
    refine ⟨a • φ + b • (χ - ψ₀), ?_⟩
    have hc : (n ℓ₀ - (ℓ₀ + 1 : ℕ)) • φ = (p : ℤ) • (χ - ψ₀) := by
      rw [smul_sub, ← hχ, hφ'eq]
      abel
    calc φ = (a * (p : ℤ) + b * (n ℓ₀ - (ℓ₀ + 1 : ℕ))) • φ := by rw [hab, one_smul]
      _ = (p : ℤ) • (a • φ) + b • ((n ℓ₀ - (ℓ₀ + 1 : ℕ)) • φ) := by
          rw [add_smul, mul_smul, mul_smul, smul_comm a (p : ℤ) φ]
      _ = (p : ℤ) • (a • φ + b • (χ - ψ₀)) := by
          rw [hc, smul_add, smul_comm b (p : ℤ) (χ - ψ₀)]
  ·
    intro ℓ hℓ hℓS hℓN
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨ψ, hψ⟩ := hT ℓ hℓ hℓS hℓN
    refine ⟨CohCarrier.heckeT N ⊤ ℓ₀ ℤ ψ - (ℓ₀ + 1) • ψ, ?_⟩
    have hcomm : CohCarrier.heckeT N ⊤ ℓ ℤ (CohCarrier.heckeT N ⊤ ℓ₀ ℤ φ)
        = CohCarrier.heckeT N ⊤ ℓ₀ ℤ (CohCarrier.heckeT N ⊤ ℓ ℤ φ) := by
      by_cases hℓℓ₀ : ℓ = ℓ₀
      · subst hℓℓ₀
        rfl
      · exact CohCarrier.heckeT_comm_of_prime N ⊤ ℓ ℓ₀ hℓ
          ((Nat.coprime_primes hℓ hℓ₀).mpr hℓℓ₀) φ

    have hTℓ : CohCarrier.heckeT N ⊤ ℓ ℤ φ = n ℓ • φ + (p : ℤ) • ψ := by rw [← hψ]; abel
    rw [hφ'def, map_sub, map_nsmul, hcomm, hTℓ, map_add, map_zsmul, map_zsmul]
    module

end HeckeAlgebra
p2m_reactivate "P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible.IntegralLift"

end CohCarrierGoingUp
p2m_reactivate "P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible.IntegralLift"

end PieceGoingUp
p2m_reactivate "P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible.IntegralLift"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)
    (S₀ : Set ℕ) (S : Finset ℕ) (n : ℕ → ℤ)
    (φ₀ : CohCarrier.H1 N H ℤ) (hφ₀par : φ₀ ∈ ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) ℤ)
    (hφ₀ : ¬ ∃ ψ : CohCarrier.H1 N H ℤ, φ₀ = (p : ℤ) • ψ)
    (hdia : ∀ σ : CongruenceSubgroup.Gamma0 N, ∃ ψ : CohCarrier.H1 N H ℤ,
      CohCarrier.diamondRaw N H ℤ σ φ₀ - φ₀ = (p : ℤ) • ψ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ ψ : CohCarrier.H1 N H ℤ, CohCarrier.heckeT N H ℓ ℤ φ₀ - n ℓ • φ₀ = (p : ℤ) • ψ)
    (k : Type) [Field k] [CharP k p] (ρbar : ResidualGaloisRep k) (hirr : ρbar.IsAbsolutelyIrreducible)
    (h3 : p = 3 → ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k)) :
    ∃ 𝔪 : Ideal (CuspForm.heckeAlgebra N 2 S₀), 𝔪.IsMaximal ∧
      (p : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₀ : ℓ ∉ S₀), ℓ ∉ S →
        CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀ - (n ℓ : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪 := by
  have _ := hφ₀par
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ℓ₀, hℓ₀, hℓ₀S, hℓ₀N, hℓ₀sq, hnoneis⟩ := ResidualGaloisRep.exists_prime_notMem_not_dvd_modEq_one_not_dvd_sub_succ p hp2 N S n k ρbar hirr htr
  haveI : NeZero ℓ₀ := ⟨hℓ₀.ne_zero⟩

  have hv : (Int.castAddHom (ZMod p)).comp φ₀ ≠ 0 := castAddHom_comp_ne_zero p φ₀ hφ₀
  have hvdia := diamondRaw_castAddHom_comp p φ₀ hdia
  have hvT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ N →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CohCarrier.heckeT N H ℓ (ZMod p) ((Int.castAddHom (ZMod p)).comp φ₀)
        = n ℓ • (Int.castAddHom (ZMod p)).comp φ₀ :=
    fun ℓ hℓ hℓS hℓN => heckeT_castAddHom_comp p S n φ₀ hT ℓ hℓ hℓS hℓN

  have hlev : CohCarrier.LevelLE N N ⊤ H 1 := ⟨dvd_rfl, one_dvd _, fun _ _ => Subgroup.mem_top _⟩
  obtain ⟨w, hwv, -, hwT⟩ := CohCarrier.InvariantExtension.exists_iDeg'_eq_of_diamondRaw_eq_of_heckeT_eq hlev S n _
    hvdia hvT hℓ₀ hℓ₀S hℓ₀N hnoneis
  have hw : w ≠ 0 := by
    rintro rfl
    exact hv (by rw [← hwv, map_zero])

  obtain ⟨φ, hφw⟩ : ∃ φ : CohCarrier.H1 N ⊤ ℤ, (Int.castAddHom (ZMod p)).comp φ = w := by
    by_cases hp3 : p = 3
    · subst hp3
      exact EllipticLift.exists_castAddHom_comp_eq_of_three N S n w hwT hℓ₀ hℓ₀S hℓ₀N hℓ₀sq
        (by exact_mod_cast hnoneis) k ρbar (h3 rfl) htr
    · exact IntegralLift.exists_castAddHom_comp_eq N p hp2 hp3 w
  obtain ⟨hφ, hφT⟩ := not_exists_eq_smul_and_congr_of_castAddHom_comp_eq p S n φ w hφw hw hwT

  exact CohCarrierGoingUp.exists_isMaximal_heckeAlgebra_of_top_of_witness N p Fact.out S₀ S n φ hφ hφT ℓ₀ hℓ₀ hℓ₀S
    hℓ₀N hℓ₀sq hnoneis

end S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible
end P2MW
export P2MW.S_CohCarrier_exists_isMaximal_heckeAlgebra_mem_of_mem_parabolicHoms_of_isAbsolutelyIrreducible (solution)

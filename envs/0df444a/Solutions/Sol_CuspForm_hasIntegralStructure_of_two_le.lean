-- Prove2me | solution 1 for CuspForm.hasIntegralStructure_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/19c3d489-62f4-5b47-9d28-a6ced44edcc7

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_ModularForm_HeckeOperatorForms
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_CuspForm_linearIndependent_complex_of_linearIndependent_int_of_periodPackage
import Theorems.Thm_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent
import Theorems.Thm_HeckeEis_exists_coeffH1par_map_ringHom
import Theorems.Thm_HeckeEis_exists_basis_coeffH1par_int_complex
import Theorems.Thm_HeckeEis_span_range_coeffH1par_map_int_complex_eq_top
import Theorems.Thm_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_coeffH1par_map_heckeT_comm
import Theorems.Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime
import Theorems.Thm_CuspForm_conjForm_heckeTLin_heckeULin_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_hasIntegralStructure_of_two_le
p2m_attr_erase "instance" "FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "simp" "HeckeEis.coe_linePow ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff"
set_option autoImplicit false

section ConjugateFormGlue

open scoped MatrixGroups ModularForm ComplexConjugate Pointwise
open UpperHalfPlane

namespace ConjFormJ

private theorem val_J_mul_mul_J (g : GL (Fin 2) ℝ) :
    ((J * g * J : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(g : Matrix (Fin 2) (Fin 2) ℝ) 0 0, -(g : Matrix (Fin 2) (Fin 2) ℝ) 0 1;
        -(g : Matrix (Fin 2) (Fin 2) ℝ) 1 0, (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

private theorem J_mul_J : (J : GL (Fin 2) ℝ) * J = 1 := by
  rw [← sq, J_sq]

private theorem J_inv : (J : GL (Fin 2) ℝ)⁻¹ = J :=
  inv_eq_of_mul_eq_one_right J_mul_J

private def flip (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -(γ 0 1); -(γ 1 0), γ 1 1], by
    have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.2
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩

private theorem flip_apply_one_zero (γ : SL(2, ℤ)) : flip γ 1 0 = -(γ 1 0) := by
  simp [flip]

private theorem flip_mem {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    flip γ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  rw [flip_apply_one_zero, Int.cast_neg, hγ, neg_zero]

private theorem mapGL_flip (γ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ (flip γ) = J * Matrix.SpecialLinearGroup.mapGL ℝ γ * J := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [val_J_mul_mul_J]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, flip]

private theorem J_mul_mul_J_mem {N : ℕ} {x : GL (Fin 2) ℝ}
    (hx : x ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    J * x * J ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  exact ⟨flip γ, flip_mem hγ, mapGL_flip γ⟩

private theorem toConjAct_J_inv_smul_Gamma0 (N : ℕ) :
    ConjAct.toConjAct (J : GL (Fin 2) ℝ)⁻¹ • (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) =
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul, J_inv]
  refine ⟨fun h => ?_, J_mul_mul_J_mem⟩
  have h' := J_mul_mul_J_mem h
  simp only [← mul_assoc] at h'
  rwa [J_mul_J, one_mul, mul_assoc, J_mul_J, mul_one] at h'

private noncomputable def conjForm {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k :=
  (CuspForm.translate f J).copy (⇑f ∣[k] J) rfl (toConjAct_J_inv_smul_Gamma0 N).symm

private theorem conjForm_apply {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    conjForm f τ = conj (f (ofComplex (-(conj (τ : ℂ))))) := by
  change (⇑f ∣[k] J) τ = _
  simp [ModularForm.slash_def, J_smul]

end ConjFormJ

namespace CuspForm p2m_export "CuspForm" "translate smul_apply ext coe_smul add_apply coe_add HasIntegralStructure heckeGenerators heckeAlgebra linearIndependent_complex_of_linearIndependent_int_of_periodPackage hasIntegralStructure_of_moduleFinite_of_linearIndependent conjForm_heckeTLin_heckeULin_comm" end CuspForm
p2m_open_scoped "CuspForm" in
private theorem CuspForm.exists_conjForm (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k → CuspForm (CongruenceSubgroup.Gamma0 N) k,
      ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane),
        ρ f τ = (starRingEnd ℂ) (f ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩) := by
  refine ⟨fun f => ConjFormJ.conjForm f, fun f τ => ?_⟩
  rw [ConjFormJ.conjForm_apply,
    UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]

end ConjugateFormGlue

noncomputable section

namespace PeriodPackagePlumbing

variable {S V : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]

private theorem exists_involution (ES : S →ₗ[ℂ] V) (ESbar : S →ₛₗ[starRingEnd ℂ] V)
    (hES : Function.Injective ES) (hESbar : Function.Injective ESbar)
    (hcompl : IsCompl (LinearMap.range ES) (LinearMap.range ESbar))
    (ρ : S → S) (hadd : ∀ f g, ρ (f + g) = ρ f + ρ g)
    (hsmul : ∀ (a : ℂ) (f : S), ρ (a • f) = (starRingEnd ℂ) a • ρ f) :
    ∃ σ : V →ₗ[ℂ] V, (∀ f, σ (ES f) = ESbar (ρ f)) ∧ (∀ g, σ (ESbar g) = ES (ρ g)) := by
  let eE := LinearEquiv.ofInjective ES hES
  let eF := LinearEquiv.ofInjective ESbar hESbar
  let σ₁ : LinearMap.range ES →ₗ[ℂ] V :=
    { toFun := fun v => ESbar (ρ (eE.symm v))
      map_add' := by
        intro v w
        show ESbar (ρ (eE.symm (v + w))) = ESbar (ρ (eE.symm v)) + ESbar (ρ (eE.symm w))
        rw [map_add, hadd, map_add]
      map_smul' := by
        intro a v
        show ESbar (ρ (eE.symm (a • v))) = a • ESbar (ρ (eE.symm v))
        rw [map_smul, hsmul, LinearMap.map_smulₛₗ, Complex.conj_conj] }
  let σ₂ : LinearMap.range ESbar →ₗ[ℂ] V :=
    { toFun := fun v => ES (ρ (eF.symm v))
      map_add' := by
        intro v w
        show ES (ρ (eF.symm (v + w))) = ES (ρ (eF.symm v)) + ES (ρ (eF.symm w))
        rw [map_add, hadd, map_add]
      map_smul' := by
        intro a v
        show ES (ρ (eF.symm (a • v))) = a • ES (ρ (eF.symm v))
        rw [LinearEquiv.map_smulₛₗ, hsmul, Complex.conj_conj, map_smul] }
  refine ⟨σ₁.coprod σ₂ ∘ₗ (Submodule.prodEquivOfIsCompl _ _ hcompl).symm.toLinearMap, ?_, ?_⟩
  · intro f
    have h : (Submodule.prodEquivOfIsCompl _ _ hcompl).symm (ES f) = (eE f, 0) := by
      simpa [eE] using Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hcompl (eE f)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h]
    show σ₁ (eE f) + σ₂ 0 = ESbar (ρ f)
    rw [map_zero, add_zero]
    show ESbar (ρ (eE.symm (eE f))) = ESbar (ρ f)
    rw [LinearEquiv.symm_apply_apply]
  · intro g
    have h : (Submodule.prodEquivOfIsCompl _ _ hcompl).symm (ESbar g) = (0, eF g) := by
      simpa [eF] using Submodule.prodEquivOfIsCompl_symm_apply_right _ _ hcompl (eF g)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h]
    show σ₁ 0 + σ₂ (eF g) = ES (ρ g)
    rw [map_zero, zero_add]
    show ES (ρ (eF.symm (eF g))) = ES (ρ g)
    rw [LinearEquiv.symm_apply_apply]

private theorem exists_eq_add (ES : S →ₗ[ℂ] V) (ESbar : S →ₛₗ[starRingEnd ℂ] V)
    (hcompl : IsCompl (LinearMap.range ES) (LinearMap.range ESbar)) (v : V) :
    ∃ f g : S, v = ES f + ESbar g := by
  have hv : v ∈ LinearMap.range ES ⊔ LinearMap.range ESbar := by
    rw [hcompl.sup_eq_top]; trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hx
  obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hy
  exact ⟨f, g, rfl⟩

private theorem exists_eq_add_involution (ES : S →ₗ[ℂ] V) (ESbar : S →ₛₗ[starRingEnd ℂ] V)
    (hcompl : IsCompl (LinearMap.range ES) (LinearMap.range ESbar)) (σ : V →ₗ[ℂ] V)
    (ρ : S → S) (hσE : ∀ f, σ (ES f) = ESbar (ρ f)) (hinv : ∀ f, ρ (ρ f) = f) (v : V) :
    ∃ f g : S, v = ES f + σ (ES g) := by
  obtain ⟨f, g, rfl⟩ := exists_eq_add ES ESbar hcompl v
  exact ⟨f, ρ g, by rw [hσE, hinv]⟩

private theorem comm_involution (ES : S →ₗ[ℂ] V) (ESbar : S →ₛₗ[starRingEnd ℂ] V)
    (hcompl : IsCompl (LinearMap.range ES) (LinearMap.range ESbar)) (σ A : V →ₗ[ℂ] V)
    (ρ T : S → S) (hσE : ∀ f, σ (ES f) = ESbar (ρ f)) (hσF : ∀ g, σ (ESbar g) = ES (ρ g))
    (hAE : ∀ f, A (ES f) = ES (T f)) (hAF : ∀ g, A (ESbar g) = ESbar (T g))
    (hρT : ∀ f, ρ (T f) = T (ρ f)) (v : V) : A (σ v) = σ (A v) := by
  obtain ⟨f, g, rfl⟩ := exists_eq_add ES ESbar hcompl v
  simp only [map_add, hσE, hσF, hAE, hAF, hρT]

private theorem exists_rat_equivFun {H : Type} [AddCommGroup H] [Module ℤ H] {t : ℕ}
    (Φ : H →+ V) (b : Module.Basis (Fin t) ℤ H) (c : Module.Basis (Fin t) ℂ V)
    (hc : ∀ i, c i = Φ (b i)) (y : H) (x : Fin t) :
    ∃ q : ℚ, c.equivFun (Φ y) x = (q : ℂ) := by
  refine ⟨((b.repr y x : ℤ) : ℚ), ?_⟩
  have hy : Φ y = c.equivFun.symm (fun i => ((b.repr y i : ℤ) : ℂ)) := by
    rw [c.equivFun_symm_apply]
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
    simpa using map_intCast_smul Φ ℤ ℂ (b.repr y i) (b i)
  rw [hy, LinearEquiv.apply_symm_apply]
  simp

end PeriodPackagePlumbing

section ConjugateFormIsAntilinear

open CongruenceSubgroup

variable {N : ℕ} {k : ℤ} {ρ : CuspForm (Gamma0 N) k → CuspForm (Gamma0 N) k}
  (hρ : ∀ (f : CuspForm (Gamma0 N) k) (τ : UpperHalfPlane),
    ρ f τ = (starRingEnd ℂ) (f ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩))

include hρ

private theorem conjForm_add (f g : CuspForm (Gamma0 N) k) : ρ (f + g) = ρ f + ρ g := by
  ext τ
  simp [hρ]

private theorem conjForm_smul (a : ℂ) (f : CuspForm (Gamma0 N) k) :
    ρ (a • f) = (starRingEnd ℂ) a • ρ f := by
  ext τ
  simp [hρ]

private theorem conjForm_conjForm (f : CuspForm (Gamma0 N) k) : ρ (ρ f) = f := by
  ext τ
  rw [hρ, hρ]
  simp only [Complex.conj_conj]
  congr 1
  ext
  simp

end ConjugateFormIsAntilinear

open CongruenceSubgroup PeriodPackagePlumbing in

private theorem linearIndependent_complex_of_linearIndependent_int_of_successor (N : ℕ) [NeZero N] (n : ℕ)
    {ι : Type} (T : ι → CuspForm.heckeAlgebra N ((n : ℤ) + 2) (∅ : Set ℕ)) (hT : LinearIndependent ℤ T) :
    LinearIndependent ℂ
      (fun i => ((T i : CuspForm.heckeAlgebra N ((n : ℤ) + 2) (∅ : Set ℕ)) :
        Module.End ℂ (CuspForm (Gamma0 N) ((n : ℤ) + 2)))) := by
  obtain ⟨ES, ESbar, hES, hESbar, hcompl, hequivT, hequivU⟩ :=
    HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime N n
  obtain ⟨Φ, hΦ⟩ := HeckeEis.exists_coeffH1par_map_ringHom (Int.castRingHom ℂ) n (Gamma0 N)
  obtain ⟨t, b, c, hc⟩ := HeckeEis.exists_basis_coeffH1par_int_complex n N Φ hΦ
  have hspan := HeckeEis.span_range_coeffH1par_map_int_complex_eq_top n N Φ hΦ
  obtain ⟨ρ, hρ⟩ := CuspForm.exists_conjForm N ((n : ℤ) + 2)
  obtain ⟨σ, hσE, hσF⟩ :=
    exists_involution ES ESbar hES hESbar hcompl ρ (conjForm_add hρ) (conjForm_smul hρ)
  have hρcomm := CuspForm.conjForm_heckeTLin_heckeULin_comm N ((n : ℤ) + 2) ρ hρ
  have hev : Function.Injective c.equivFun.toLinearMap := c.equivFun.injective
  have hLrat : ∀ v ∈ Φ.range, ∀ x : Fin t, ∃ q : ℚ, c.equivFun.toLinearMap v x = (q : ℂ) := by
    intro v hv x
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hv
    exact exists_rat_equivFun Φ b c hc y x
  have hLspan : ∀ f, ES f ∈ Submodule.span ℂ (Φ.range : Set _) := by
    intro f
    rw [AddMonoidHom.coe_range, hspan]
    trivial
  have hLcover : ∀ v ∈ Φ.range, ∃ f g, v = ES f + σ (ES g) := fun v _ =>
    exists_eq_add_involution ES ESbar hcompl σ ρ hσE (conjForm_conjForm hρ) v

  have hops : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ∃ A : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) →ₗ[ℂ]
          HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype),
        (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
            (w : Gamma0 N → HeckeEis.BinaryForm ℂ n)
              = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)
                  (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) z ∧
            A (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) ∧
        (∀ v ∈ Φ.range, A v ∈ Φ.range) := by
    intro ℓ hℓ
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨A, hA⟩ := HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun N ℓ
      ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ)
      (HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℂ n N ℓ)
    obtain ⟨AZ, hAZ⟩ := HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun N ℓ
      ((HeckeEis.binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℤ n ℓ)
      (HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℤ n N ℓ)
    refine ⟨A, hA, ?_⟩
    intro v hv
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hv
    rw [HeckeEis.coeffH1par_map_heckeT_comm (Int.castRingHom ℂ) n N ℓ Φ hΦ AZ hAZ A hA y]
    exact AddMonoidHom.mem_range.mpr ⟨AZ y, rfl⟩
  have htwin : ∀ s ∈ CuspForm.heckeGenerators N ((n : ℤ) + 2) (∅ : Set ℕ),
      ∃ A : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) →ₗ[ℂ]
          HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype),
        (∀ f, ES (s f) = A (ES f)) ∧ (∀ v, A (σ v) = σ (A v)) ∧ (∀ v ∈ Φ.range, A v ∈ Φ.range) := by
    intro s hs
    simp only [CuspForm.heckeGenerators, Set.mem_union, Set.mem_setOf_eq] at hs
    rcases hs with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩
    · obtain ⟨A, hA, hAL⟩ := hops ℓ hℓ
      obtain ⟨hAE, hAF⟩ := hequivT ℓ hℓ hℓN A hA
      exact ⟨A, fun f => (hAE f).symm,
        comm_involution ES ESbar hcompl σ A ρ _ hσE hσF hAE hAF (hρcomm.1 hℓ hℓN), hAL⟩
    · obtain ⟨A, hA, hAL⟩ := hops q hq
      obtain ⟨hAE, hAF⟩ := hequivU q hq hqN A hA
      exact ⟨A, fun f => (hAE f).symm,
        comm_involution ES ESbar hcompl σ A ρ _ hσE hσF hAE hAF (hρcomm.2 hqN), hAL⟩
  exact CuspForm.linearIndependent_complex_of_linearIndependent_int_of_periodPackage N ((n : ℤ) + 2)
    c.equivFun.toLinearMap hev ES hES σ Φ.range hLrat hLspan hLcover htwin T hT

end

section HeckeAlgebraFiniteness

open CongruenceSubgroup

private theorem exists_int_equivFun {V : Type} [AddCommGroup V] [Module ℂ V]
    {H : Type} [AddCommGroup H] [Module ℤ H] {t : ℕ}
    (Φ : H →+ V) (b : Module.Basis (Fin t) ℤ H) (c : Module.Basis (Fin t) ℂ V)
    (hc : ∀ i, c i = Φ (b i)) (y : H) (x : Fin t) :
    ∃ m : ℤ, c.equivFun (Φ y) x = (m : ℂ) := by
  refine ⟨b.repr y x, ?_⟩
  have hy : Φ y = c.equivFun.symm (fun i => ((b.repr y i : ℤ) : ℂ)) := by
    rw [c.equivFun_symm_apply]
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc]
    simpa using map_intCast_smul Φ ℤ ℂ (b.repr y i) (b i)
  rw [hy, LinearEquiv.apply_symm_apply]

private theorem End_ext_of_isCompl {S V : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
    (ES : S →ₗ[ℂ] V) (ESbar : S →ₛₗ[starRingEnd ℂ] V)
    (hcompl : IsCompl (LinearMap.range ES) (LinearMap.range ESbar))
    (A₁ A₂ : Module.End ℂ V) (h₁ : ∀ f, A₁ (ES f) = A₂ (ES f)) (h₂ : ∀ f, A₁ (ESbar f) = A₂ (ESbar f)) :
    A₁ = A₂ := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ LinearMap.range ES ⊔ LinearMap.range ESbar := by
    rw [hcompl.sup_eq_top]
    trivial
  obtain ⟨y, ⟨f, rfl⟩, z, ⟨g, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, h₁, h₂]

private def intMatrixCast (t : ℕ) : (Fin t → Fin t → ℤ) →ₗ[ℤ] (Fin t → Fin t → ℂ) where
  toFun M := fun i j => ((M i j : ℤ) : ℂ)
  map_add' M M' := by
    funext i j
    simp
  map_smul' r M := by
    funext i j
    simp

private theorem moduleFinite_of_transport {S V H : Type} [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup H] [Module ℤ H] (𝕋 : Subalgebra ℤ (Module.End ℂ S))
    (ES : S →ₗ[ℂ] V) (ESbar : S →ₛₗ[starRingEnd ℂ] V) (hES : Function.Injective ES)
    (hcompl : IsCompl (LinearMap.range ES) (LinearMap.range ESbar))
    (Φ : H →+ V) {t : ℕ} (b : Module.Basis (Fin t) ℤ H) (c : Module.Basis (Fin t) ℂ V) (hc : ∀ i, c i = Φ (b i))
    (A : ∀ s : Module.End ℂ S, s ∈ 𝕋 → Module.End ℂ V)
    (hAE : ∀ s hs f, A s hs (ES f) = ES (s f)) (hAF : ∀ s hs f, A s hs (ESbar f) = ESbar (s f))
    (hAL : ∀ s hs, ∀ v ∈ Set.range Φ, A s hs v ∈ Set.range Φ) :
    Module.Finite ℤ 𝕋 := by
  have huniq : ∀ (s : 𝕋) (B : Module.End ℂ V),
      (∀ f, B (ES f) = ES (s.1 f)) → (∀ f, B (ESbar f) = ESbar (s.1 f)) → A s.1 s.2 = B := by
    intro s B hBE hBF
    exact End_ext_of_isCompl ES ESbar hcompl _ _ (fun f => by rw [hAE, hBE]) (fun f => by rw [hAF, hBF])
  let Ψ : 𝕋 →ₗ[ℤ] Module.End ℂ V :=
    { toFun := fun s => A s.1 s.2
      map_add' := fun x y => huniq (x + y) (A x.1 x.2 + A y.1 y.2)
        (fun f => by rw [LinearMap.add_apply, hAE, hAE, Subalgebra.coe_add, LinearMap.add_apply, map_add])
        (fun f => by rw [LinearMap.add_apply, hAF, hAF, Subalgebra.coe_add, LinearMap.add_apply, map_add])
      map_smul' := fun r x => huniq (r • x) (r • A x.1 x.2)
        (fun f => by rw [LinearMap.smul_apply, hAE, Subalgebra.coe_smul, LinearMap.smul_apply, map_zsmul])
        (fun f => by rw [LinearMap.smul_apply, hAF, Subalgebra.coe_smul, LinearMap.smul_apply, map_zsmul]) }
  have hΨ : ∀ s, Ψ s = A s.1 s.2 := fun _ => rfl
  let coords : Module.End ℂ V →ₗ[ℤ] (Fin t → Fin t → ℂ) :=
    { toFun := fun B => fun i j => c.equivFun (B (c j)) i
      map_add' := fun B B' => by
        funext i j
        simp only [LinearMap.add_apply, map_add, Pi.add_apply]
      map_smul' := fun r B => by
        funext i j
        simp only [LinearMap.smul_apply, map_zsmul, Pi.smul_apply, RingHom.id_apply] }
  have hcoords : ∀ B i j, coords B i j = c.equivFun (B (c j)) i := fun _ _ _ => rfl
  let θ := coords.comp Ψ
  have hθ : Function.Injective θ := by
    intro x y hxy
    have hAxy : A x.1 x.2 = A y.1 y.2 := by
      apply c.ext
      intro j
      apply c.equivFun.injective
      funext i
      have := congrFun (congrFun hxy i) j
      simpa [θ, hcoords, hΨ] using this
    apply Subtype.ext
    apply LinearMap.ext
    intro f
    apply hES
    rw [← hAE x.1 x.2 f, hAxy, hAE]
  have hint : ∀ x, θ x ∈ LinearMap.range (intMatrixCast t) := by
    intro x
    have hL : ∀ j, ∃ y, Φ y = A x.1 x.2 (c j) := fun j => hAL x.1 x.2 (c j) ⟨b j, (hc j).symm⟩
    choose y hy using hL
    have hm : ∀ i j, ∃ m : ℤ, θ x i j = (m : ℂ) := by
      intro i j
      obtain ⟨m, hm⟩ := exists_int_equivFun Φ b c hc (y j) i
      refine ⟨m, ?_⟩
      simp only [θ, LinearMap.comp_apply, hcoords, hΨ, ← hy j]
      exact hm
    choose M hM using hm
    refine ⟨M, ?_⟩
    funext i j
    exact (hM i j).symm
  haveI : IsNoetherian ℤ (LinearMap.range (intMatrixCast t)) := inferInstance
  exact Module.Finite.of_injective (θ.codRestrict (LinearMap.range (intMatrixCast t)) hint)
    (fun x y h => hθ (by simpa using congrArg Subtype.val h))

open PeriodPackagePlumbing in

private theorem moduleFinite_heckeAlgebra_of_successor (N : ℕ) [NeZero N] (n : ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N ((n : ℤ) + 2) (∅ : Set ℕ)) := by
  obtain ⟨ES, ESbar, hES, hESbar, hcompl, hequivT, hequivU⟩ :=
    HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime N n
  obtain ⟨Φ, hΦ⟩ := HeckeEis.exists_coeffH1par_map_ringHom (Int.castRingHom ℂ) n (Gamma0 N)
  obtain ⟨t, b, c, hc⟩ := HeckeEis.exists_basis_coeffH1par_int_complex n N Φ hΦ

  have hP : ∀ s ∈ CuspForm.heckeAlgebra N ((n : ℤ) + 2) (∅ : Set ℕ),
      ∃ A : Module.End ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
        (∀ f, A (ES f) = ES (s f)) ∧ (∀ f, A (ESbar f) = ESbar (s f)) ∧
        (∀ v ∈ Set.range Φ, A v ∈ Set.range Φ) := by
    intro s hs
    refine Algebra.adjoin_induction (p := fun s _ => ∃ A :
        Module.End ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
        (∀ f, A (ES f) = ES (s f)) ∧ (∀ f, A (ESbar f) = ESbar (s f)) ∧
        (∀ v ∈ Set.range Φ, A v ∈ Set.range Φ)) ?_ ?_ ?_ ?_ hs
    ·
      intro g hg
      simp only [CuspForm.heckeGenerators, Set.mem_union, Set.mem_setOf_eq] at hg
      have hop : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime),
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
          ∃ A : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) →ₗ[ℂ]
              HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype),
            (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
                ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)),
                (w : Gamma0 N → HeckeEis.BinaryForm ℂ n)
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)
                      (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) z ∧
                A (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) ∧
            (∀ v ∈ Set.range Φ, A v ∈ Set.range Φ) := by
        intro ℓ hℓ
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        obtain ⟨A, hA⟩ := HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun N ℓ
          ((HeckeEis.binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ)
          (HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℂ n N ℓ)
        obtain ⟨AZ, hAZ⟩ := HeckeEis.exists_coeffH1par_linearMap_coeffHeckeFun N ℓ
          ((HeckeEis.binaryFormRepSL ℤ n).comp (Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℤ n ℓ)
          (HeckeEis.binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj ℤ n N ℓ)
        refine ⟨A, hA, ?_⟩
        rintro v ⟨y, rfl⟩
        rw [HeckeEis.coeffH1par_map_heckeT_comm (Int.castRingHom ℂ) n N ℓ Φ hΦ AZ hAZ A hA y]
        exact ⟨AZ y, rfl⟩
      rcases hg with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩
      · obtain ⟨A, hA, hAL⟩ := hop ℓ hℓ
        obtain ⟨hAE, hAF⟩ := hequivT ℓ hℓ hℓN A hA
        exact ⟨A, hAE, hAF, hAL⟩
      · obtain ⟨A, hA, hAL⟩ := hop q hq
        obtain ⟨hAE, hAF⟩ := hequivU q hq hqN A hA
        exact ⟨A, hAE, hAF, hAL⟩
    ·
      intro r
      refine ⟨(r : Module.End ℂ _), ?_, ?_, ?_⟩
      · intro f
        simp only [algebraMap_int_eq, eq_intCast, Module.End.intCast_apply, map_zsmul]
      · intro f
        simp only [algebraMap_int_eq, eq_intCast, Module.End.intCast_apply, map_zsmul]
      · rintro v ⟨y, rfl⟩
        exact ⟨r • y, by rw [Module.End.intCast_apply, map_zsmul]⟩
    ·
      rintro x y _ _ ⟨A, hAE, hAF, hAL⟩ ⟨B, hBE, hBF, hBL⟩
      refine ⟨A + B, ?_, ?_, ?_⟩
      · intro f
        simp only [LinearMap.add_apply, hAE, hBE, map_add]
      · intro f
        simp only [LinearMap.add_apply, hAF, hBF, map_add]
      · rintro v ⟨y, rfl⟩
        obtain ⟨y₁, hy₁⟩ := hAL (Φ y) ⟨y, rfl⟩
        obtain ⟨y₂, hy₂⟩ := hBL (Φ y) ⟨y, rfl⟩
        exact ⟨y₁ + y₂, by rw [map_add, hy₁, hy₂, LinearMap.add_apply]⟩
    ·
      rintro x y _ _ ⟨A, hAE, hAF, hAL⟩ ⟨B, hBE, hBF, hBL⟩
      refine ⟨A * B, ?_, ?_, ?_⟩
      · intro f
        rw [Module.End.mul_apply, hBE, hAE, Module.End.mul_apply]
      · intro f
        rw [Module.End.mul_apply, hBF, hAF, Module.End.mul_apply]
      · intro v hv
        rw [Module.End.mul_apply]
        exact hAL _ (hBL v hv)
  choose A hAE hAF hAL using hP
  exact moduleFinite_of_transport _ ES ESbar hES hcompl Φ b c hc A hAE hAF hAL

end HeckeAlgebraFiniteness

private theorem hasIntegralStructure_of_two_le_of_successor (N : ℕ) [NeZero N] (k : ℤ) (hk : 2 ≤ k) :
    CuspForm.HasIntegralStructure N k := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 2 := ⟨(k - 2).toNat, by omega⟩
  exact CuspForm.hasIntegralStructure_of_moduleFinite_of_linearIndependent N ((n : ℤ) + 2) (by omega)
    (moduleFinite_heckeAlgebra_of_successor N n)
    (fun T hT => linearIndependent_complex_of_linearIndependent_int_of_successor N n T hT)

open _root_.CuspForm _root_.P2MW.S_CuspForm_hasIntegralStructure_of_two_le.CuspForm in
theorem solution (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 2 ≤ k) : HasIntegralStructure N' k :=
  hasIntegralStructure_of_two_le_of_successor N' k hk

end S_CuspForm_hasIntegralStructure_of_two_le
end P2MW
export P2MW.S_CuspForm_hasIntegralStructure_of_two_le (solution)

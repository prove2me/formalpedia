-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_isMaximal_two_ringHom_of_succ_of_map_T_eq_zero_of_five_le_or_exists_prime_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8c012c89-baa5-5512-b1c6-fb2d1a1e6a75

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_CuspForm_heckeAlgebra_exists_mem_modPCusp_isModPEigen_of_ringHom
import Theorems.Thm_ModPForms_modPCusp_le_modPMod
import Theorems.Thm_ModPForms_mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero
import Theorems.Thm_ModPForms_mem_modPMod_two_of_mem_modPMod_four_of_forall_coeff_three_mul_eq_zero_of_exists_prime_dvd_mod_three_eq_two
import Theorems.Thm_WeierstrassCurve_mem_modPCusp_of_mem_modPMod_of_isModPEigen_pow_mul_apOfModel_of_modRepIsIrreducible
import Theorems.Thm_CuspForm_heckeAlgebra_exists_ringHom_apply_eq_of_isModPEigen_of_heckeU_eq_smul
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_hasIntegralStructure_of_two_le
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_isMaximal_two_ringHom_of_succ_of_map_T_eq_zero_of_five_le_or_exists_prime_dvd
p2m_attr_erase "instance" "HeckeEis.instFiniteProjLineCusps ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk ModularCurve.ProjectiveLine.map_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec FrobeniusEndo.linePencil_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
open CuspForm
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace Face3Asm
open ModPForms

theorem forall_coeff_mul_eq_zero_of_heckePS_eq_zero (p : ℕ) (F : Type) [Field F] [CharP F p] (k : ℤ)
    (hk : k ≠ 1) (φ : PowerSeries F) (h : heckePS k p φ = 0) (n : ℕ) :
    PowerSeries.coeff (p * n) φ = 0 := by
  have hpF : (p : F) = 0 := CharP.cast_eq_zero F p
  have hk' : k - 1 ≠ 0 := sub_ne_zero.mpr hk
  have := congrArg (PowerSeries.coeff n) h
  rw [heckePS, PowerSeries.coeff_mk, map_zero, hpF, zero_zpow _ hk'] at this
  simpa [mul_comm p n] using this

theorem heckePS_weight_p_add_one_eq_two
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p] (ℓ : ℕ) (φ : PowerSeries F) :
    heckePS ((p : ℤ) + 1) ℓ φ = heckePS 2 ℓ φ := by
  unfold heckePS
  congr 1
  funext n
  congr 2
  have h1 : ((p : ℤ) + 1 - 1) = ((p : ℕ) : ℤ) := by omega
  have h2 : ((2 : ℤ) - 1) = ((1 : ℕ) : ℤ) := by norm_num
  have h3 : (ℓ : F) ^ p = ℓ := by simpa only [frobenius_def] using map_natCast (frobenius F p) ℓ
  rw [h1, h2, zpow_natCast, zpow_natCast, pow_one, h3]

theorem isModPEigen_weight_p_add_one_iff_two
    (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (N : ℕ) (S₀ : Set ℕ) (φ : PowerSeries F) (lam : ℕ → F) :
    IsModPEigen N S₀ ((p : ℤ) + 1) φ lam ↔ IsModPEigen N S₀ 2 φ lam := by
  unfold IsModPEigen
  simp only [heckePS_weight_p_add_one_eq_two p]

theorem IsModPEigen.mono {F : Type} [Field F] {N : ℕ} {S S' : Set ℕ} (hSS' : S ⊆ S') {k : ℤ}
    {φ : PowerSeries F} {lam : ℕ → F} (h : IsModPEigen N S k φ lam) : IsModPEigen N S' k φ lam :=
  ⟨h.1, fun ℓ hℓ hℓN hℓS' => h.2 ℓ hℓ hℓN fun hℓS => hℓS' (hSS' hℓS)⟩

theorem ker_isMaximal (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ) (k : ℤ) (hk : 2 ≤ k)
    (F : Type) [Field F] [CharP F p] (θ : heckeAlgebra N k S →+* F) : (RingHom.ker θ).IsMaximal := by
  haveI : Module.Finite ℤ (heckeAlgebra N k S) :=
    CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra
      (CuspForm.hasIntegralStructure_of_two_le N k hk) (by omega) S
  haveI : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime θ
  haveI : Algebra.IsIntegral ℤ (heckeAlgebra N k S) := Algebra.IsIntegral.of_finite ℤ _
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ)
  haveI : ((RingHom.ker θ).comap (algebraMap ℤ (heckeAlgebra N k S))).IsPrime := Ideal.comap_isPrime _ _
  apply IsPrime.to_maximal_ideal
  intro hbot
  have hp : (p : ℤ) ∈ (RingHom.ker θ).comap (algebraMap ℤ (heckeAlgebra N k S)) := by
    rw [Ideal.mem_comap, RingHom.mem_ker, map_natCast, map_natCast, CharP.cast_eq_zero]
  rw [hbot, Ideal.mem_bot] at hp
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

end Face3Asm

open ModPForms Face3Asm in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (hKatz : 5 ≤ p ∨ ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (i : ℕ)
    (𝔪' : Ideal (CuspForm.heckeAlgebra N' ((p : ℤ) + 1) S₀)) (h𝔪' : 𝔪'.IsMaximal)
    (hp𝔪' : (p : CuspForm.heckeAlgebra N' ((p : ℤ) + 1) S₀) ∈ 𝔪')
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        CuspForm.heckeAlgebra.T hℓ hℓN hℓS -
          ((ℓ ^ i * W.apOfModel ℓ : ℤ) : CuspForm.heckeAlgebra N' ((p : ℤ) + 1) S₀) ∈ 𝔪')
    (F : Type) [Field F] [CharP F p]
    (θ : CuspForm.heckeAlgebra N' ((p : ℤ) + 1) (S₀ \ {p}) →+* F)
    (hθker : RingHom.ker (θ.comp (Subalgebra.inclusion
      (CuspForm.heckeAlgebra_mono Set.diff_subset)).toRingHom) = 𝔪')
    (hap0 : θ (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpN'
      (by simp : p ∉ S₀ \ {p})) = 0)
    :
    ∃ (𝔪₂ : Ideal (heckeAlgebra N' 2 S₀)) (θ₂ : heckeAlgebra N' 2 (S₀ \ {p}) →+* F),
      𝔪₂.IsMaximal ∧ (p : heckeAlgebra N' 2 S₀) ∈ 𝔪₂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
        W.IsGoodPrimeFor ℓ →
          heckeAlgebra.T hℓ hℓN hℓS -
            ((ℓ ^ i * W.apOfModel ℓ : ℤ) : heckeAlgebra N' 2 S₀) ∈ 𝔪₂) ∧
      RingHom.ker (θ₂.comp (Subalgebra.inclusion
        (heckeAlgebra_mono Set.diff_subset)).toRingHom) = 𝔪₂ ∧
      θ₂ (heckeAlgebra.T (Fact.out : p.Prime) hpN' (by simp : p ∉ S₀ \ {p})) = 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S₀ \ {p}),
        θ₂ (heckeAlgebra.T hℓ hℓN hℓS) = θ (heckeAlgebra.T hℓ hℓN hℓS) := by
  classical
  have hp : p.Prime := Fact.out
  have hpS : p ∉ S₀ \ {p} := by simp
  have hk2 : (2 : ℤ) ≤ (p : ℤ) + 1 := by have := hp.two_le; omega

  obtain ⟨φ, lam, hφc, heig, hlam, heigU⟩ :=
    CuspForm.heckeAlgebra.exists_mem_modPCusp_isModPEigen_of_ringHom p N' (S₀ \ {p}) ((p : ℤ) + 1) hk2 F θ

  have hap0' : θ (heckeAlgebra.T hp hpN' hpS) = 0 := hap0
  have hTp0 : heckePS ((p : ℤ) + 1) p φ = 0 := by
    have h := heig.2 p hp hpN' hpS
    rw [hlam p hp hpN' hpS, hap0', zero_smul] at h
    exact h
  have hT : ∀ n : ℕ, PowerSeries.coeff (p * n) φ = 0 :=
    forall_coeff_mul_eq_zero_of_heckePS_eq_zero p F ((p : ℤ) + 1) (by omega) φ hTp0

  have hφM : φ ∈ modPMod N' ((p : ℤ) + 1) F := ModPForms.modPCusp_le_modPMod N' _ F hφc
  have hφ2 : φ ∈ modPMod N' 2 F := by
    by_cases hp5 : 5 ≤ p
    · exact ModPForms.mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero p hp hp5 N' hpN' F φ hφM hT
    · have hp3 : p = 3 := by
        have h2 := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · rfl
        · exact absurd hp (by decide)
      obtain hε := hKatz.resolve_left hp5
      subst hp3
      have hφ4 : φ ∈ modPMod N' 4 F := by simpa using hφM
      exact ModPForms.mem_modPMod_two_of_mem_modPMod_four_of_forall_coeff_three_mul_eq_zero_of_exists_prime_dvd_mod_three_eq_two
        N' hε hpN' F φ hφ4 hT

  have heig2 : IsModPEigen N' (S₀ \ {p}) 2 φ lam :=
    (isModPEigen_weight_p_add_one_iff_two p N' (S₀ \ {p}) φ lam).1 heig

  have hmu : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
      lam ℓ = ((ℓ ^ i * W.apOfModel ℓ : ℤ) : F) := by
    intro ℓ hℓ hℓS hℓN hgood
    have hℓS' : ℓ ∉ S₀ \ {p} := fun h => hℓS h.1
    have hmem : heckeAlgebra.T hℓ hℓN hℓS -
        ((ℓ ^ i * W.apOfModel ℓ : ℤ) : heckeAlgebra N' ((p : ℤ) + 1) S₀) ∈
        RingHom.ker (θ.comp (Subalgebra.inclusion (heckeAlgebra_mono Set.diff_subset)).toRingHom) := by
      rw [hθker]
      exact hocc ℓ hℓ hℓS hℓN hgood
    rw [RingHom.mem_ker, map_sub, map_intCast, sub_eq_zero] at hmem
    have hincl : Subalgebra.inclusion (heckeAlgebra_mono Set.diff_subset)
        (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' ((p : ℤ) + 1) S₀) =
        (heckeAlgebra.T hℓ hℓN hℓS' : heckeAlgebra N' ((p : ℤ) + 1) (S₀ \ {p})) :=
      Subtype.ext rfl
    rw [hlam ℓ hℓ hℓN hℓS', ← hmem]
    change θ _ = θ (Subalgebra.inclusion _ _)
    rw [hincl]

  have hφ2c : φ ∈ modPCusp N' 2 F :=
    WeierstrassCurve.mem_modPCusp_of_mem_modPMod_of_isModPEigen_pow_mul_apOfModel_of_modRepIsIrreducible
      p hp2 W hΔ hirr N' hpN' S₀ hS₀fin hS₀p 2 le_rfl i F φ lam hφ2 (Face3Asm.IsModPEigen.mono Set.diff_subset heig2) hmu

  let mu : ℕ → F := fun q =>
    if h : q.Prime ∧ q ∣ N' ∧ q ∉ S₀ \ {p} then θ (heckeAlgebra.U h.1 h.2.1 h.2.2) else 0
  have heigU' : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N') (hqS : q ∉ S₀ \ {p}),
      PowerSeries.heckeU q φ = mu q • φ := by
    intro q hq hqN hqS
    simp only [mu, dif_pos (show q.Prime ∧ q ∣ N' ∧ q ∉ S₀ \ {p} from ⟨hq, hqN, hqS⟩)]
    exact heigU q hq hqN hqS
  obtain ⟨θ₂, hθ₂T, -⟩ :=
    CuspForm.heckeAlgebra.exists_ringHom_apply_eq_of_isModPEigen_of_heckeU_eq_smul p N' (S₀ \ {p}) 2 le_rfl F
      φ lam mu hφ2c heig2 heigU'

  refine ⟨RingHom.ker (θ₂.comp (Subalgebra.inclusion (heckeAlgebra_mono Set.diff_subset)).toRingHom), θ₂,
    ker_isMaximal p N' S₀ 2 le_rfl F _, ?_, ?_, rfl, ?_, ?_⟩
  ·
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  ·
    intro ℓ hℓ hℓS hℓN hgood
    have hℓS' : ℓ ∉ S₀ \ {p} := fun h => hℓS h.1
    rw [RingHom.mem_ker, map_sub, map_intCast, sub_eq_zero]
    have hincl : Subalgebra.inclusion (heckeAlgebra_mono Set.diff_subset)
        (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' 2 S₀) =
        (heckeAlgebra.T hℓ hℓN hℓS' : heckeAlgebra N' 2 (S₀ \ {p})) :=
      Subtype.ext rfl
    change θ₂ (Subalgebra.inclusion _ _) = _
    rw [hincl, hθ₂T ℓ hℓ hℓN hℓS', hmu ℓ hℓ hℓS hℓN hgood]
  ·
    exact (hθ₂T p _ hpN' _).trans ((hlam p hp hpN' hpS).trans hap0')
  ·
    intro ℓ hℓ hℓN hℓS
    exact (hθ₂T ℓ hℓ hℓN hℓS).trans (hlam ℓ hℓ hℓN hℓS)

end S_CuspForm_heckeAlgebra_exists_isMaximal_two_ringHom_of_succ_of_map_T_eq_zero_of_five_le_or_exists_prime_dvd
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_isMaximal_two_ringHom_of_succ_of_map_T_eq_zero_of_five_le_or_exists_prime_dvd (solution)

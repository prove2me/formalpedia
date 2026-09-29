-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dcaadbe1-1871-5508-8e89-c99183b43699

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure
p2m_attr_erase "instance" "HeckeEis.instFiniteProjLineCusps ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "simp" "HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk ModularCurve.ProjectiveLine.map_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.symPoly_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial IsLocalRing

namespace CuspForm
p2m_export "CuspForm" "ext heckeAlgebra moduleFinite_heckeAlgebra"
namespace heckeAlgebra
namespace Desc
p2m_open "CuspForm.heckeAlgebra CuspForm"

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]

theorem isIntegral_algHom_apply (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    (χ : A →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪)) (a : A) :
    IsIntegral 𝒪 (χ a) :=
  (Algebra.IsIntegral.isIntegral (R := 𝒪) a).map χ

scoped instance moduleFinite_range (M : ℕ) [NeZero M] (S' : Set ℕ)
    (chig : CuspForm.heckeAlgebra M 2 S' →+* ℂ) : Module.Finite ℤ chig.range := by
  haveI := CuspForm.moduleFinite_heckeAlgebra M 2 S'
  exact Module.Finite.of_surjective (chig.rangeRestrict.toIntAlgHom).toLinearMap
    chig.rangeRestrict_surjective

theorem isIntegral_ringHom_range_apply (M : ℕ) [NeZero M] (S' : Set ℕ)
    (chig : CuspForm.heckeAlgebra M 2 S' →+* ℂ)
    (ι : chig.range →+* AlgebraicClosure (FractionRing 𝒪)) (z : chig.range) :
    IsIntegral 𝒪 (ι z) := by
  obtain ⟨f, hfm, hfz⟩ : IsIntegral ℤ z := Algebra.IsIntegral.isIntegral (R := ℤ) z
  refine ⟨f.map (Int.castRingHom 𝒪), hfm.map _, ?_⟩
  rw [eval₂_map]
  have h1 : (algebraMap 𝒪 (AlgebraicClosure (FractionRing 𝒪))).comp (Int.castRingHom 𝒪) =
      ι.comp (algebraMap ℤ chig.range) := RingHom.ext_int _ _
  rw [h1, ← Polynomial.hom_eval₂, hfz, map_zero]

theorem finiteDimensional_adjoin_range_union (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    (χ : A →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪)) (M : ℕ) [NeZero M] (S' : Set ℕ)
    (chig : CuspForm.heckeAlgebra M 2 S' →+* ℂ)
    (ι : chig.range →+* AlgebraicClosure (FractionRing 𝒪)) :
    FiniteDimensional (FractionRing 𝒪)
      (IntermediateField.adjoin (FractionRing 𝒪)
        (Set.range χ ∪ Set.range ι : Set (AlgebraicClosure (FractionRing 𝒪)))) := by
  have h1 : FiniteDimensional (FractionRing 𝒪)
      (IntermediateField.adjoin (FractionRing 𝒪) (Set.range (χ : A →+* AlgebraicClosure (FractionRing 𝒪)))) :=
    RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range (R := 𝒪)
      (χ : A →+* AlgebraicClosure (FractionRing 𝒪)) fun r => ⟨algebraMap 𝒪 (FractionRing 𝒪) r, by
        rw [AlgHom.coe_toRingHom, AlgHom.commutes]
        exact (IsScalarTower.algebraMap_apply 𝒪 (FractionRing 𝒪) (AlgebraicClosure (FractionRing 𝒪)) r).symm⟩
  have h2 : FiniteDimensional (FractionRing 𝒪)
      (IntermediateField.adjoin (FractionRing 𝒪) (Set.range ι)) :=
    RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range (R := ℤ) ι fun r =>
      ⟨algebraMap ℤ (FractionRing 𝒪) r, by rw [eq_intCast, eq_intCast, map_intCast, map_intCast]⟩
  have hχ : Set.range (χ : A →+* AlgebraicClosure (FractionRing 𝒪)) = Set.range χ := rfl
  rw [hχ] at h1
  rw [IntermediateField.adjoin_union]
  exact IntermediateField.finiteDimensional_sup _ _

theorem dvr_package
    (L' : IntermediateField (FractionRing 𝒪) (AlgebraicClosure (FractionRing 𝒪)))
    [FiniteDimensional (FractionRing 𝒪) L'] :
    ∃ (_ : IsDiscreteValuationRing (integralClosure 𝒪 L'))
      (_ : IsAdicComplete (maximalIdeal (integralClosure 𝒪 L')) (integralClosure 𝒪 L'))
      (_ : Finite (ResidueField (integralClosure 𝒪 L'))),
      Module.Finite 𝒪 (integralClosure 𝒪 L') ∧ CharZero (integralClosure 𝒪 L') ∧
        IsLocalHom (algebraMap 𝒪 (integralClosure 𝒪 L')) := by
  obtain ⟨hmf, hdvr, hcpl⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal 𝒪 (FractionRing 𝒪) L'
  haveI := hdvr
  haveI := hmf

  have hinjL : Function.Injective (algebraMap 𝒪 L') := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (FractionRing 𝒪) L']
    exact (algebraMap (FractionRing 𝒪) L').injective.comp (IsFractionRing.injective 𝒪 (FractionRing 𝒪))
  have hinj : Function.Injective (algebraMap 𝒪 (integralClosure 𝒪 L')) := by
    rw [IsScalarTower.algebraMap_eq 𝒪 (integralClosure 𝒪 L') L', RingHom.coe_comp] at hinjL
    exact hinjL.of_comp
  haveI : FaithfulSMul 𝒪 (integralClosure 𝒪 L') :=
    (faithfulSMul_iff_algebraMap_injective 𝒪 (integralClosure 𝒪 L')).mpr hinj
  haveI hloc : IsLocalHom (algebraMap 𝒪 (integralClosure 𝒪 L')) := inferInstance
  have hfin : Finite (ResidueField (integralClosure 𝒪 L')) :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪) inferInstance
  exact ⟨hdvr, hcpl, hfin, hmf, inferInstance, hloc⟩

theorem main (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    (χ : A →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪))
    (M : ℕ) [NeZero M] (S' : Set ℕ) (chig : CuspForm.heckeAlgebra M 2 S' →+* ℂ)
    (ι : chig.range →+* AlgebraicClosure (FractionRing 𝒪)) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪'))
      (j : 𝒪' →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪)) (ψ : A →ₐ[𝒪] 𝒪') (ι' : chig.range →+* 𝒪'),
      Function.Injective j ∧ (∀ a : A, j (ψ a) = χ a) ∧ (∀ z : chig.range, j (ι' z) = ι z) := by

  let L' : IntermediateField (FractionRing 𝒪) (AlgebraicClosure (FractionRing 𝒪)) :=
    IntermediateField.adjoin (FractionRing 𝒪) (Set.range χ ∪ Set.range ι)
  haveI : FiniteDimensional (FractionRing 𝒪) L' := finiteDimensional_adjoin_range_union A χ M S' chig ι
  obtain ⟨hdvr, hcpl, hfin, hmf, hcz, hloc⟩ := dvr_package (𝒪 := 𝒪) L'

  have hχL : ∀ a : A, χ a ∈ L' := fun a =>
    IntermediateField.subset_adjoin _ _ (Or.inl ⟨a, rfl⟩)
  have hιL : ∀ z : chig.range, ι z ∈ L' := fun z =>
    IntermediateField.subset_adjoin _ _ (Or.inr ⟨z, rfl⟩)
  have hχI : ∀ a : A, (⟨χ a, hχL a⟩ : L') ∈ integralClosure 𝒪 L' := fun a => by
    rw [mem_integralClosure_iff]
    exact (isIntegral_algHom_iff (IntermediateField.val L' |>.restrictScalars 𝒪)
      (IntermediateField.val L').toRingHom.injective).mp (isIntegral_algHom_apply A χ a)
  have hιI : ∀ z : chig.range, (⟨ι z, hιL z⟩ : L') ∈ integralClosure 𝒪 L' := fun z => by
    rw [mem_integralClosure_iff]
    exact (isIntegral_algHom_iff (IntermediateField.val L' |>.restrictScalars 𝒪)
      (IntermediateField.val L').toRingHom.injective).mp (isIntegral_ringHom_range_apply M S' chig ι z)

  let j : integralClosure 𝒪 L' →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪) :=
    ((IntermediateField.val L').restrictScalars 𝒪).comp (integralClosure 𝒪 L').val
  let ψ : A →ₐ[𝒪] integralClosure 𝒪 L' :=
    { toFun := fun a => ⟨⟨χ a, hχL a⟩, hχI a⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp
      commutes' := fun r => by
        apply Subtype.ext; apply Subtype.ext
        simp only [AlgHom.commutes]
        rfl }
  let ι' : chig.range →+* integralClosure 𝒪 L' :=
    { toFun := fun z => ⟨⟨ι z, hιL z⟩, hιI z⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp }
  refine ⟨integralClosure 𝒪 L', inferInstance, inferInstance, hdvr, hcpl, hfin, hcz, inferInstance, hmf,
    hloc, j, ψ, ι', ?_, fun a => rfl, fun z => rfl⟩
  exact (IntermediateField.val L').toRingHom.injective.comp Subtype.val_injective

end CuspForm.heckeAlgebra.Desc
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm.heckeAlgebra P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm.heckeAlgebra.Desc"
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm.heckeAlgebra"
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm"

end
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm.heckeAlgebra P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure.CuspForm.heckeAlgebra.Desc"

open IsLocalRing in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    (χ : A →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪))
    (M : ℕ) [NeZero M] (S' : Set ℕ) (chig : CuspForm.heckeAlgebra M 2 S' →+* ℂ)
    (ι : chig.range →+* AlgebraicClosure (FractionRing 𝒪)) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪'))
      (j : 𝒪' →ₐ[𝒪] AlgebraicClosure (FractionRing 𝒪)) (ψ : A →ₐ[𝒪] 𝒪') (ι' : chig.range →+* 𝒪'),
      Function.Injective j ∧ (∀ a : A, j (ψ a) = χ a) ∧ (∀ z : chig.range, j (ι' z) = ι z) :=
  CuspForm.heckeAlgebra.Desc.main A χ M S' chig ι

end S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_dvr_algHom_comp_eq_and_ringHom_comp_eq_of_algHom_algebraicClosure (solution)

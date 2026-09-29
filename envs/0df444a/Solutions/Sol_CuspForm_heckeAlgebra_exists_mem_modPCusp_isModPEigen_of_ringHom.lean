-- Prove2me | solution 1 for CuspForm.heckeAlgebra.exists_mem_modPCusp_isModPEigen_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4b5f96c8-38a4-58dd-9500-95e0131a0138

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_CuspForm_mem_intLattice_iff
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra
import Theorems.Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_CuspForm_hasIntegralStructure_of_two_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_exists_mem_modPCusp_isModPEigen_of_ringHom
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

open CuspForm ModPForms

namespace G1Eig

open Submodule in
theorem exists_addMonoidHom_semilinear {R N F : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (hfaith : ∀ r : R, (∀ x : N, r • x = 0) → r = 0)
    [Field F] (θ : R →+* F) {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hθ : ∀ r ∈ 𝔪, θ r = 0) :
    ∃ Λ : N →+ F, Λ ≠ 0 ∧ ∀ (r : R) (x : N), Λ (r • x) = θ r * Λ x := by
  classical

  have hne : (𝔪 • ⊤ : Submodule R N) ≠ ⊤ := by
    intro htop
    obtain ⟨r, hr1, hr0⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 (⊤ : Submodule R N)
        Module.Finite.fg_top (by rw [htop])
    have hr : r = 0 := hfaith r fun x => hr0 x mem_top
    rw [hr, zero_sub] at hr1
    have h1 : (1 : R) ∈ 𝔪 := by simpa using 𝔪.neg_mem hr1
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one 𝔪).mpr h1)
  obtain ⟨x₀, -, hx₀⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)

  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hq₀ : Submodule.Quotient.mk (p := (𝔪 • ⊤ : Submodule R N)) x₀ ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hx₀
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (R ⧸ 𝔪) hq₀

  let θbar : R ⧸ 𝔪 →+* F := Ideal.Quotient.lift 𝔪 θ hθ
  refine ⟨θbar.toAddMonoidHom.comp
      (f.toAddMonoidHom.comp (Submodule.mkQ (𝔪 • ⊤ : Submodule R N)).toAddMonoidHom), ?_, ?_⟩
  · intro h0
    have h1 := DFunLike.congr_fun h0 x₀
    change θbar (f (Submodule.Quotient.mk x₀)) = 0 at h1
    exact hf ((map_eq_zero_iff θbar θbar.injective).mp h1)
  · intro r x
    change θbar (f (Submodule.Quotient.mk (r • x))) = θ r * θbar (f (Submodule.Quotient.mk x))
    rw [← Module.Quotient.mk_smul_mk (M := N) (I := 𝔪), map_smul, smul_eq_mul, map_mul,
      Ideal.Quotient.lift_mk]

theorem exists_addMonoidHom_semilinear_of_ringHom {R N F : Type*} [CommRing R] [AddCommGroup N]
    [Module.Finite ℤ N] (σ : R →+* Module.End ℤ N) (hfaith : ∀ r : R, σ r = 0 → r = 0)
    [Field F] (θ : R →+* F) {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hθ : ∀ r ∈ 𝔪, θ r = 0) :
    ∃ Λ : N →+ F, Λ ≠ 0 ∧ ∀ (r : R) (x : N), Λ (σ r x) = θ r * Λ x := by
  letI : Module R N := Module.compHom N σ
  have hsmul : ∀ (r : R) (x : N), r • x = σ r x := fun _ _ => rfl
  haveI : IsScalarTower ℤ R N :=
    ⟨fun m r x => by rw [hsmul, hsmul, map_zsmul, LinearMap.smul_apply]⟩
  haveI : Module.Finite R N := Module.Finite.of_restrictScalars_finite ℤ R N
  obtain ⟨Λ, h0, h⟩ := exists_addMonoidHom_semilinear (R := R) (N := N)
    (fun r hr => hfaith r (LinearMap.ext fun x => hr x)) θ h𝔪 hθ
  exact ⟨Λ, h0, fun r x => h r x⟩

end G1Eig

namespace G1EigApp

variable {N' : ℕ} [NeZero N'] {k : ℤ}

abbrev V (N' : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma0 N') k

theorem isAddTorsionFree_V (N' : ℕ) (k : ℤ) : IsAddTorsionFree (V N' k) where
  nsmul_right_injective n hn a b hab := by
    have h : (n : ℂ) • a = (n : ℂ) • b := by
      simpa only [Nat.cast_smul_eq_nsmul] using hab
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hn) h

theorem hΓ (N' : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N')).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N'

omit [NeZero N'] in

theorem qCoeff_add (f g : V N' k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑f + ⇑g) n = ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_add one_pos (hΓ N') f g, map_add]

omit [NeZero N'] in

theorem qCoeff_smul (c : ℂ) (f : V N' k) (n : ℕ) :
    ModularFormClass.qCoeff (c • ⇑f) n = c * ModularFormClass.qCoeff f n := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_smul one_pos (hΓ N') c f, map_smul, smul_eq_mul]

abbrev L (N' : ℕ) (k : ℤ) := ↥(CuspForm.intLattice N' k)

private abbrev _root_.G1EigApp.T (N' : ℕ) [NeZero N'] (k : ℤ) (S₀ : Set ℕ) := ↥(heckeAlgebra N' k S₀)

p2m_export "G1EigApp" "T"

abbrev D (N' : ℕ) (k : ℤ) := Module.Dual ℤ (L N' k)

noncomputable def ic (f : L N' k) (n : ℕ) : ℤ :=
  ((CuspForm.mem_intLattice_iff (f : V N' k)).mp f.2 n).choose

omit [NeZero N'] in
theorem ic_spec (f : L N' k) (n : ℕ) :
    ModularFormClass.qCoeff (f : V N' k) n = (ic f n : ℂ) :=
  ((CuspForm.mem_intLattice_iff (f : V N' k)).mp f.2 n).choose_spec

theorem ic_add (f g : L N' k) (n : ℕ) : ic (f + g) n = ic f n + ic g n := by
  have h : ((ic (f + g) n : ℤ) : ℂ) = ((ic f n + ic g n : ℤ) : ℂ) := by
    rw [← ic_spec, Int.cast_add, ← ic_spec, ← ic_spec, Submodule.coe_add, CuspForm.coe_add,
      qCoeff_add]
  exact_mod_cast h

noncomputable def cf (n : ℕ) : Module.Dual ℤ (L N' k) :=
  (AddMonoidHom.mk' (fun f : L N' k => ic f n) (fun f g => ic_add f g n)).toIntLinearMap

@[scoped simp] theorem cf_apply (n : ℕ) (f : L N' k) : cf n f = ic f n := rfl

noncomputable def actL {S₀ : Set ℕ} (hk : 1 ≤ k) (t : heckeAlgebra N' k S₀) : L N' k →ₗ[ℤ] L N' k where
  toFun f := ⟨(t : Module.End ℂ (V N' k)) (f : V N' k),
    CuspForm.mem_intLattice_of_mem_heckeAlgebra hk t.2 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
  map_smul' m f := by
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, map_zsmul, eq_intCast, Int.cast_id]

@[scoped simp] theorem coe_actL {S₀ : Set ℕ} (hk : 1 ≤ k) (t : heckeAlgebra N' k S₀) (f : L N' k) :
    ((actL hk t f : L N' k) : V N' k) = (t : Module.End ℂ (V N' k)) (f : V N' k) := rfl

theorem actL_mul {S₀ : Set ℕ} (hk : 1 ≤ k) (t s : heckeAlgebra N' k S₀) :
    actL hk (t * s) = actL hk t ∘ₗ actL hk s := by
  ext f
  rfl

theorem actL_comm {S₀ : Set ℕ} (hk : 1 ≤ k) (t s : heckeAlgebra N' k S₀) :
    actL hk t ∘ₗ actL hk s = actL hk s ∘ₗ actL hk t := by
  rw [← actL_mul, ← actL_mul, mul_comm]

noncomputable def σ {S₀ : Set ℕ} (hk : 1 ≤ k) :
    heckeAlgebra N' k S₀ →+* Module.End ℤ (Module.Dual ℤ (L N' k)) where
  toFun t := (actL hk t).dualMap
  map_one' := by
    have h : actL hk (1 : heckeAlgebra N' k S₀) = LinearMap.id := by ext f; rfl
    rw [h, LinearMap.dualMap_id]
    rfl
  map_mul' t s := by
    rw [actL_mul, actL_comm, ← LinearMap.dualMap_comp_dualMap]
    rfl
  map_zero' := by
    have h : actL hk (0 : heckeAlgebra N' k S₀) = 0 := by
      ext f
      simp only [coe_actL, ZeroMemClass.coe_zero, LinearMap.zero_apply]
    apply LinearMap.ext; intro g; apply LinearMap.ext; intro f
    simp [LinearMap.dualMap_apply, h]
  map_add' t s := by
    have h : actL hk (t + s) = actL hk t + actL hk s := by
      ext f
      simp only [coe_actL, Subalgebra.coe_add, LinearMap.add_apply, Submodule.coe_add]
    apply LinearMap.ext; intro g; apply LinearMap.ext; intro f
    simp [LinearMap.dualMap_apply, h]

theorem σ_apply {S₀ : Set ℕ} (hk : 1 ≤ k) (t : heckeAlgebra N' k S₀) (g : Module.Dual ℤ (L N' k))
    (f : L N' k) : σ hk t g f = g (actL hk t f) := by
  simp [σ, LinearMap.dualMap_apply]

theorem ic_heckeT {S₀ : Set ℕ} (hk : 1 ≤ k) (hk2 : 2 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (hℓS : ℓ ∉ S₀) (f : L N' k) (n : ℕ) :
    ic (actL hk (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) f) n =
      ic f (n * ℓ) + if ℓ ∣ n then (ℓ : ℤ) ^ (k - 1).toNat * ic f (n / ℓ) else 0 := by
  have hkm : ((ℓ : ℂ) ^ (k - 1 : ℤ)) = (ℓ : ℂ) ^ (k - 1).toNat := by
    rw [← zpow_natCast]
    congr 1
    omega
  have h : ((ic (actL hk (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) f) n : ℤ) : ℂ) =
      ((ic f (n * ℓ) + if ℓ ∣ n then (ℓ : ℤ) ^ (k - 1).toNat * ic f (n / ℓ) else 0 : ℤ) : ℂ) := by
    rw [← ic_spec, coe_actL, heckeAlgebra.coe_T]
    change ModularFormClass.qCoeff (ModularForm.heckeT k ℓ ⇑(f : V N' k)) n = _
    rw [ModularFormClass.qCoeff_heckeT (f : V N' k) (hΓ N') hℓ.ne_zero n,
      ModularForm.coeffHeckeT_apply, ic_spec]
    split_ifs with hd
    · rw [ic_spec, hkm]
      push_cast
      ring
    · push_cast
      ring
  exact_mod_cast h

theorem σ_T_cf {S₀ : Set ℕ} (hk : 1 ≤ k) (hk2 : 2 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (hℓS : ℓ ∉ S₀) (n : ℕ) :
    σ hk (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) (cf n) =
      cf (n * ℓ) + if ℓ ∣ n then ((ℓ : ℤ) ^ (k - 1).toNat) • cf (n / ℓ) else 0 := by
  apply LinearMap.ext
  intro f
  rw [σ_apply, cf_apply, ic_heckeT hk hk2 hℓ hℓN hℓS f n]
  split_ifs with hd
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, cf_apply, smul_eq_mul]
  · simp only [add_zero, cf_apply]

theorem ic_heckeU {S₀ : Set ℕ} (hk : 1 ≤ k) {q : ℕ} (hq : q.Prime) (hqN : q ∣ N')
    (hqS : q ∉ S₀) (f : L N' k) (n : ℕ) :
    ic (actL hk (heckeAlgebra.U hq hqN hqS : heckeAlgebra N' k S₀) f) n = ic f (n * q) := by
  have h : ((ic (actL hk (heckeAlgebra.U hq hqN hqS : heckeAlgebra N' k S₀) f) n : ℤ) : ℂ) =
      ((ic f (n * q) : ℤ) : ℂ) := by
    rw [← ic_spec, coe_actL, heckeAlgebra.coe_U]
    change ModularFormClass.qCoeff (ModularForm.heckeU k q ⇑(f : V N' k)) n = _
    rw [ModularFormClass.qCoeff_heckeU (f : V N' k) (hΓ N') hq.ne_zero n,
      ModularForm.coeffHeckeU_apply, ic_spec]
  exact_mod_cast h

theorem σ_U_cf {S₀ : Set ℕ} (hk : 1 ≤ k) {q : ℕ} (hq : q.Prime) (hqN : q ∣ N')
    (hqS : q ∉ S₀) (n : ℕ) :
    σ hk (heckeAlgebra.U hq hqN hqS : heckeAlgebra N' k S₀) (cf n) = cf (n * q) := by
  apply LinearMap.ext
  intro f
  rw [σ_apply, cf_apply, ic_heckeU hk hq hqN hqS f n, cf_apply]

end G1EigApp
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_exists_mem_modPCusp_isModPEigen_of_ringHom.G1EigApp"

set_option synthInstance.maxHeartbeats 1600000 in
open G1EigApp in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ)
    (k : ℤ) (hk : 2 ≤ k) (F : Type) [Field F] [CharP F p]
    (θ : heckeAlgebra N k S →+* F) :
    ∃ (φ : PowerSeries F) (lam : ℕ → F),
      φ ∈ modPCusp N k F ∧ IsModPEigen N S k φ lam ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
          lam ℓ = θ (heckeAlgebra.T hℓ hℓN hℓS)) ∧
        ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
          PowerSeries.heckeU q φ = θ (heckeAlgebra.U hq hqN hqS) • φ := by
  classical
  have hk1 : (1 : ℤ) ≤ k := by omega
  have hint : HasIntegralStructure N k := CuspForm.hasIntegralStructure_of_two_le N k hk

  haveI : Module.Finite ℤ (T N k S) :=
    CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hint hk1 S
  let 𝔪 : Ideal (T N k S) := RingHom.ker θ
  have hθ0 : ∀ r ∈ 𝔪, θ r = 0 := fun r hr => (RingHom.mem_ker).mp hr
  have h𝔪 : 𝔪.IsMaximal := by
    haveI : 𝔪.IsPrime := RingHom.ker_isPrime θ
    haveI : Algebra.IsIntegral ℤ (T N k S) := Algebra.IsIntegral.of_finite ℤ (T N k S)
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ)
    haveI : (𝔪.comap (algebraMap ℤ (T N k S))).IsPrime := Ideal.comap_isPrime _ _
    apply IsPrime.to_maximal_ideal
    intro hbot
    have hp : (p : ℤ) ∈ 𝔪.comap (algebraMap ℤ (T N k S)) := by
      rw [Ideal.mem_comap, RingHom.mem_ker, map_natCast, map_natCast, CharP.cast_eq_zero]
    rw [hbot, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

  haveI : IsAddTorsionFree (V N k) := isAddTorsionFree_V N k
  haveI : Module.Finite ℤ (L N k) := Module.Finite.iff_fg.mpr (CuspForm.intLattice_fg N k)
  haveI : Module.IsTorsionFree ℤ (L N k) := inferInstance
  haveI : Module.Free ℤ (L N k) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite ℤ (D N k) := Module.Finite.of_basis (Module.finBasis ℤ (L N k)).dualBasis

  have hfaith : ∀ t : T N k S, σ hk1 t = 0 → t = 0 := by
    intro t ht
    apply Subtype.ext
    change (t : Module.End ℂ (V N k)) = 0
    apply CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice hint
    intro f hf
    have hzero : actL hk1 t ⟨f, hf⟩ = 0 := by
      rw [← Module.forall_dual_apply_eq_zero_iff ℤ (actL hk1 t ⟨f, hf⟩)]
      intro g
      have h1 : σ hk1 t g (⟨f, hf⟩ : L N k) = 0 := by rw [ht, LinearMap.zero_apply, LinearMap.zero_apply]
      rwa [σ_apply] at h1
    simpa using congrArg (fun x : L N k => (x : V N k)) hzero
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    G1Eig.exists_addMonoidHom_semilinear_of_ringHom (σ hk1 (S₀ := S)) hfaith θ h𝔪 hθ0

  let φ : PowerSeries F := PowerSeries.mk fun n => Λ (cf n)
  have hφc : ∀ n, PowerSeries.coeff n φ = Λ (cf n) := fun n => PowerSeries.coeff_mk _ _
  let lam : ℕ → F := fun ℓ =>
    if h : ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S then θ (heckeAlgebra.T h.1 h.2.1 h.2.2) else 0
  have heigen : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      heckePS k ℓ φ = θ (heckeAlgebra.T hℓ hℓN hℓS) • φ := by
    intro ℓ hℓ hℓN hℓS
    have hkm : ((ℓ : F) ^ (k - 1 : ℤ)) = (ℓ : F) ^ (k - 1).toNat := by
      rw [← zpow_natCast]
      congr 1
      omega
    ext n
    rw [map_smul, smul_eq_mul, hφc, ← hΛ, σ_T_cf hk1 hk hℓ hℓN hℓS n]
    unfold heckePS
    rw [PowerSeries.coeff_mk, hφc]
    split_ifs with hd
    · rw [map_add, map_zsmul, hφc, zsmul_eq_mul, hkm]
      push_cast
      ring
    · rw [add_zero, add_zero]
  have heigenU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
      PowerSeries.heckeU q φ = θ (heckeAlgebra.U hq hqN hqS) • φ := by
    intro q hq hqN hqS
    ext n
    rw [PowerSeries.coeff_heckeU, map_smul, smul_eq_mul, hφc, hφc, ← hΛ, σ_U_cf hk1 hq hqN hqS n,
      mul_comm q n]

  let bL := Module.finBasis ℤ (L N k)
  let red : Fin (Module.finrank ℤ (L N k)) → PowerSeries (F) := fun j =>
    PowerSeries.mk fun n => ((ic (bL j) n : ℤ) : F)
  have hred : ∀ j, red j ∈ modPCusp N k (F) := fun j =>
    Submodule.subset_span ⟨((bL j : L N k) : V N k), ic (bL j), fun n => ic_spec _ _, rfl⟩
  have hΛcf : ∀ n, Λ (cf n) = ∑ j, (ic (bL j) n : F) * Λ (bL.coord j) := by
    intro n
    conv_lhs => rw [← bL.sum_dual_apply_smul_coord (cf n)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, zsmul_eq_mul, cf_apply]
  have hφsum : φ = ∑ j, Λ (bL.coord j) • red j := by
    ext n
    rw [hφc, hΛcf, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, PowerSeries.coeff_mk, smul_eq_mul, mul_comm]
  have hφmem : φ ∈ modPCusp N k (F) := by
    rw [hφsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hred j)

  have hφne : φ ≠ 0 := by

    have hex : ∃ j, Λ (bL.coord j) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hΛ0
      have hlin : Λ.toIntLinearMap = 0 := by
        refine bL.dualBasis.ext fun j => ?_
        rw [LinearMap.zero_apply, Module.Basis.coe_dualBasis]
        exact hall j
      ext g
      exact LinearMap.congr_fun hlin g
    obtain ⟨j₀, hj₀⟩ := hex
    intro hφ0
    have hcoef : ∀ n, ∑ j, (ic (bL j) n : F) * Λ (bL.coord j) = 0 := fun n => by
      rw [← hΛcf, ← hφc, hφ0, map_zero]

    letI : Algebra (ZMod p) F := ZMod.algebra F p
    obtain ⟨μ, hμ⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hj₀
    set w : Fin (Module.finrank ℤ (L N k)) → ZMod p := fun j => μ (Λ (bL.coord j))
    have hw : ∀ n, ∑ j, (ic (bL j) n : ZMod p) * w j = 0 := by
      intro n
      have h := congrArg μ (hcoef n)
      rw [map_zero, map_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← map_intCast (algebraMap (ZMod p) (F)), ← Algebra.smul_def, map_smul,
        smul_eq_mul]

    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    let c : Fin (Module.finrank ℤ (L N k)) → ℤ := fun j => ((w j).val : ℤ)
    have hc : ∀ j, (c j : ZMod p) = w j := fun j => by
      simp [c]
    let x : L N k := ∑ j, c j • bL j
    have hx : ∀ n, ic x n = ∑ j, c j * ic (bL j) n := by
      intro n
      rw [← cf_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, zsmul_eq_mul, cf_apply, Int.cast_id]
    have hdvd : ∀ n, (p : ℤ) ∣ ic x n := by
      intro n
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hx, Int.cast_sum]
      rw [← hw n]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Int.cast_mul, hc, mul_comm]
    choose d hd using hdvd

    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    set y : V N k := (p : ℂ)⁻¹ • (x : V N k) with hy_def
    have hy : y ∈ CuspForm.intLattice N k := by
      rw [CuspForm.mem_intLattice_iff]
      intro n
      refine ⟨d n, ?_⟩
      rw [hy_def, CuspForm.IsGLPos.coe_smul, qCoeff_smul, ic_spec, hd n]
      push_cast
      field_simp
    have hxy : x = (p : ℤ) • (⟨y, hy⟩ : L N k) := by
      apply Subtype.ext
      change (x : V N k) = ((p : ℤ) • (⟨y, hy⟩ : L N k) : L N k)
      rw [Submodule.coe_smul_of_tower]
      change (x : V N k) = (p : ℤ) • y
      rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, hy_def, smul_inv_smul₀ hp0]

    have hcoord : c j₀ = (p : ℤ) * bL.repr ⟨y, hy⟩ j₀ := by
      have h1 : bL.repr x j₀ = c j₀ := congrFun (bL.repr_sum_self c) j₀
      rw [← h1, hxy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]
    have hw0 : w j₀ = 0 := by
      rw [← hc, hcoord]
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    exact hμ hw0

  refine ⟨φ, lam, hφmem, ⟨hφne, ?_⟩, ?_, heigenU⟩
  · intro ℓ hℓ hℓN hℓS
    have hl : lam ℓ = θ (heckeAlgebra.T hℓ hℓN hℓS) := by
      simp only [lam, dif_pos (show ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S from ⟨hℓ, hℓN, hℓS⟩)]
    rw [hl]
    exact heigen ℓ hℓ hℓN hℓS
  · intro ℓ hℓ hℓN hℓS
    simp only [lam, dif_pos (show ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S from ⟨hℓ, hℓN, hℓS⟩)]

end S_CuspForm_heckeAlgebra_exists_mem_modPCusp_isModPEigen_of_ringHom
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_exists_mem_modPCusp_isModPEigen_of_ringHom (solution)

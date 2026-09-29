-- Prove2me | solution 1 for CuspForm.exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fcd30e8b-a363-5514-8bb1-67cab6950b10

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_CuspForm_atkinLehnerLin_atkinLehnerLin
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModPForms_eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two
import Theorems.Thm_CuspForm_exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff
import Theorems.Thm_ModPForms_eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsElliptic_tateBase Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul FreyPackage.ModMCarrier.coe_rescaleLin_apply Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false

noncomputable section

open CuspForm

namespace CuspFormAlSlashDenomAux

section Coeff

variable {N : ℕ} {k : ℤ}

private theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

private theorem qCoeff_add' (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n = ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma0 N) f g,
    map_add]

private theorem qCoeff_zero' (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) k)) n = 0 := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]

private theorem qCoeff_smul' (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) n = c * ModularFormClass.qCoeff f n := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma0 N) c f, map_smul,
    smul_eq_mul]

private def qCoeffAddHom (n : ℕ) : CuspForm (CongruenceSubgroup.Gamma0 N) k →+ ℂ where
  toFun f := ModularFormClass.qCoeff f n
  map_zero' := qCoeff_zero' n
  map_add' f g := qCoeff_add' f g n

private theorem qCoeff_sub' (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f - g)) n = ModularFormClass.qCoeff f n - ModularFormClass.qCoeff g n :=
  show qCoeffAddHom n (f - g) = qCoeffAddHom n f - qCoeffAddHom n g from map_sub _ _ _

private theorem qCoeff_zsmul' (m : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(m • f)) n = m * ModularFormClass.qCoeff f n := by
  show qCoeffAddHom n (m • f) = m * qCoeffAddHom n f
  rw [map_zsmul, zsmul_eq_mul]

private theorem qCoeff_sum' {ι : Type} (s : Finset ι) (g : ι → CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(∑ i ∈ s, g i)) n = ∑ i ∈ s, ModularFormClass.qCoeff (g i) n := by
  show qCoeffAddHom n (∑ i ∈ s, g i) = ∑ i ∈ s, qCoeffAddHom n (g i)
  rw [map_sum]

private theorem qCoeff_heckeTLin' {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (heckeTLin k hℓ hℓN f) n =
      ModularForm.coeffHeckeT k ℓ (ModularFormClass.qCoeff f) n := by
  rw [coe_heckeTLin_apply]
  exact ModularFormClass.qCoeff_heckeT f (one_mem_strictPeriods_Gamma0 N) hℓ.ne_zero n

private theorem qCoeff_heckeULin' [NeZero N] {ℓ : ℕ} (hℓ : ℓ ≠ 0) (hℓN : ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (heckeULin k hℓN f) n = ModularFormClass.qCoeff f (n * ℓ) := by
  rw [coe_heckeULin_apply]
  exact ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods_Gamma0 N) hℓ n

private theorem exists_int_qCoeff_of_mem_intLattice {f : CuspForm (CongruenceSubgroup.Gamma0 N) k}
    (hf : f ∈ intLattice N k) (n : ℕ) : ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ) := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx n
  | zero => exact ⟨0, by rw [qCoeff_zero', Int.cast_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [qCoeff_add', ha, hb, Int.cast_add]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨a * b, by rw [qCoeff_zsmul', hb, Int.cast_mul]⟩

private theorem mem_intLattice_of_int_qCoeff {f : CuspForm (CongruenceSubgroup.Gamma0 N) k}
    (hf : ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)) : f ∈ intLattice N k :=
  Submodule.subset_span hf

private theorem heckeTLin_mem_intLattice_two {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f ∈ intLattice N 2) :
    heckeTLin 2 hℓ hℓN f ∈ intLattice N 2 := by
  apply mem_intLattice_of_int_qCoeff
  intro n
  obtain ⟨a, ha⟩ := exists_int_qCoeff_of_mem_intLattice hf (n * ℓ)
  obtain ⟨b, hb⟩ := exists_int_qCoeff_of_mem_intLattice hf (n / ℓ)
  rw [qCoeff_heckeTLin', ModularForm.coeffHeckeT_apply, ha]
  by_cases hdiv : ℓ ∣ n
  · refine ⟨a + ℓ * b, ?_⟩
    rw [if_pos hdiv, hb, show (2 : ℤ) - 1 = 1 from rfl, zpow_one]
    push_cast
    ring
  · exact ⟨a, by rw [if_neg hdiv, add_zero]⟩

open Classical in

private def icoef (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) : ℤ :=
  if h : ∃ m : ℤ, ModularFormClass.qCoeff g n = (m : ℂ) then h.choose else 0

private theorem icoef_spec {g : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hg : g ∈ intLattice N k) (n : ℕ) :
    ModularFormClass.qCoeff g n = (icoef g n : ℂ) := by
  have h := exists_int_qCoeff_of_mem_intLattice hg n
  rw [icoef, dif_pos h]
  exact h.choose_spec

end Coeff

section Red

variable {N : ℕ} {k : ℤ} (ℓ : ℕ)

private def red (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) : PowerSeries (ZMod ℓ) :=
  PowerSeries.mk fun n => ((icoef g n : ℤ) : ZMod ℓ)

private theorem coeff_red (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    PowerSeries.coeff n (red ℓ g) = ((icoef g n : ℤ) : ZMod ℓ) :=
  PowerSeries.coeff_mk _ _

private theorem red_mem_modPCusp [Fact ℓ.Prime] {g : CuspForm (CongruenceSubgroup.Gamma0 N) k}
    (hg : g ∈ intLattice N k) :
    red ℓ g ∈ ModPForms.modPCusp N k (ZMod ℓ) :=
  Submodule.subset_span ⟨g, icoef g, fun n => icoef_spec hg n, rfl⟩

private theorem exists_eq_smul_of_red_eq_zero (hℓ : ℓ ≠ 0) {g : CuspForm (CongruenceSubgroup.Gamma0 N) k}
    (hg : g ∈ intLattice N k) (hred : red ℓ g = 0) :
    ∃ g' : CuspForm (CongruenceSubgroup.Gamma0 N) k, g' ∈ intLattice N k ∧ g = (ℓ : ℤ) • g' := by
  have hdvd : ∀ n, (ℓ : ℤ) ∣ icoef g n := fun n => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← coeff_red, hred, map_zero]
  choose c hc using hdvd
  have hℓC : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ
  refine ⟨(ℓ : ℂ)⁻¹ • g, mem_intLattice_of_int_qCoeff fun n => ⟨c n, ?_⟩, ?_⟩
  · rw [qCoeff_smul', icoef_spec hg, hc n]
    push_cast
    field_simp
  · rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, Int.cast_natCast, mul_inv_cancel₀ hℓC, one_smul]

end Red

section PS

variable {F : Type} [Field F]

private def expandV (p : ℕ) (φ : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) φ else 0

private theorem coeff_expandV (p : ℕ) (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (expandV p φ) = if p ∣ n then PowerSeries.coeff (n / p) φ else 0 :=
  PowerSeries.coeff_mk _ _

private theorem coeff_mul_expandV {p : ℕ} (hp : 0 < p) (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff (n * p) (expandV p φ) = PowerSeries.coeff n φ := by
  rw [coeff_expandV, if_pos (Dvd.intro_left n rfl), Nat.mul_div_cancel n hp]

private theorem eq_zero_of_expandV_eq_zero {p : ℕ} (hp : 0 < p) {φ : PowerSeries F} (h : expandV p φ = 0) : φ = 0 := by
  ext n
  rw [← coeff_mul_expandV hp φ n, h, map_zero, map_zero]

private theorem thetaPS_expandV (p : ℕ) [CharP F p] (φ : PowerSeries F) : ModPForms.thetaPS (expandV p φ) = 0 := by
  ext n
  simp only [ModPForms.thetaPS, PowerSeries.coeff_mk, coeff_expandV, map_zero]
  split_ifs with hpn
  · obtain ⟨c, rfl⟩ := hpn
    rw [Nat.cast_mul, CharP.cast_eq_zero F p, zero_mul, zero_mul]
  · rw [mul_zero]

end PS

section Spans

variable (N : ℕ) [NeZero N] (F : Type) [Field F]

private theorem eq_zero_of_expandV_eq_of_mem_modPCusp (p : ℕ) [hpF : Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N)
    (φ : PowerSeries (ZMod p)) {ψ : PowerSeries (ZMod p)} (hψ : ψ ∈ ModPForms.modPCusp N 2 (ZMod p))
    (h : expandV p φ = ψ) : ψ = 0 := by
  have hθ : ModPForms.thetaPS ψ = 0 := by rw [← h, thetaPS_expandV]
  exact ModPForms.eq_zero_of_thetaPS_eq_zero_of_mem_modPCusp_two p hpF.out hp2 N hpN (ZMod p) ψ hψ hθ

end Spans

section RatDescent

private theorem exists_theta : ∃ θ : ℂ →ₗ[ℚ] ℂ,
    (∀ r : ℚ, θ (r : ℂ) = 0) ∧ (∀ z : ℂ, θ z = 0 → ∃ r : ℚ, z = (r : ℂ)) ∧
      ∀ (z : ℂ) (r : ℚ), θ (z * r) = θ z * r := by
  set ι : ℚ →ₗ[ℚ] ℂ := Algebra.linearMap ℚ ℂ with hι
  have hιapp : ∀ r : ℚ, ι r = (r : ℂ) := fun r => by simp [hι, Algebra.linearMap_apply]
  obtain ⟨π, hπ⟩ := ι.exists_leftInverse_of_injective
    ((LinearMap.ker_eq_bot (f := ι)).mpr fun x y hxy => by
      rw [hιapp, hιapp] at hxy
      exact_mod_cast hxy)
  have hπι : ∀ r : ℚ, π (r : ℂ) = r := fun r => by
    have h := LinearMap.congr_fun hπ r
    rw [LinearMap.comp_apply, LinearMap.id_apply, hιapp] at h
    exact h
  refine ⟨LinearMap.id - ι.comp π, fun r => ?_, fun z hz => ?_, fun z r => ?_⟩
  · rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hπι, hιapp, sub_self]
  · refine ⟨π z, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, sub_eq_zero, hιapp] at hz
    exact hz
  · have h1 : z * (r : ℂ) = r • z := by rw [Rat.smul_def, mul_comm]
    rw [h1, map_smul, Rat.smul_def, mul_comm]

variable {N : ℕ} [NeZero N]

private theorem exists_nsmul_mem_intLattice_of_rat_qCoeff (z : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hz : ∀ n : ℕ, ∃ r : ℚ, ModularFormClass.qCoeff z n = (r : ℂ)) :
    ∃ D : ℕ, 0 < D ∧ ((D : ℤ) • z) ∈ intLattice N 2 := by
  classical
  obtain ⟨G, hG⟩ := CuspForm.intLattice_fg N 2
  have hGL : ∀ g ∈ (G : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2)), g ∈ intLattice N 2 := fun g hg => by
    rw [← hG]; exact Submodule.subset_span hg

  have htop : Submodule.span ℂ (G : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = ⊤ := by
    have h := CuspForm.hasIntegralStructure_two N
    unfold CuspForm.HasIntegralStructure at h
    refine le_antisymm le_top ?_
    rw [← h, Submodule.span_le]
    intro f hf
    rw [SetLike.mem_coe, ← hG] at hf
    exact Submodule.span_le_restrictScalars (R := ℤ) (S := ℂ)
      (s := (G : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) hf

  obtain ⟨b, hbG, hbspan, hbli⟩ := exists_linearIndependent ℂ (G : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
  have hbfin : b.Finite := G.finite_toSet.subset hbG
  haveI : Fintype b := hbfin.fintype
  set t : Finset (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := hbfin.toFinset with ht
  have htb : ∀ g, g ∈ t ↔ g ∈ b := fun g => hbfin.mem_toFinset
  have htL : ∀ g ∈ t, g ∈ intLattice N 2 := fun g hg => hGL g (hbG ((htb g).mp hg))
  have hzt : z ∈ Submodule.span ℂ (t : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by
    rw [show (t : Set _) = b from hbfin.coe_toFinset, hbspan, htop]
    exact Submodule.mem_top
  obtain ⟨c, -, hcz⟩ := Submodule.mem_span_finset.mp hzt

  obtain ⟨θ, hθrat, hθker, hθmul⟩ := exists_theta
  have hθc : ∀ g ∈ t, θ (c g) = 0 := by
    have hq : ∀ n, ModularFormClass.qCoeff (⇑(∑ g ∈ t, θ (c g) • g)) n = 0 := by
      intro n
      obtain ⟨r, hr⟩ := hz n
      rw [qCoeff_sum']
      calc ∑ g ∈ t, ModularFormClass.qCoeff (⇑(θ (c g) • g)) n
          = ∑ g ∈ t, θ (c g * ModularFormClass.qCoeff g n) := by
            refine Finset.sum_congr rfl fun g hg => ?_
            rw [qCoeff_smul', icoef_spec (htL g hg), show ((icoef g n : ℤ) : ℂ) = ((icoef g n : ℚ) : ℂ) by norm_cast,
              hθmul]
        _ = θ (∑ g ∈ t, c g * ModularFormClass.qCoeff g n) := (map_sum θ _ _).symm
        _ = θ (ModularFormClass.qCoeff z n) := by
            rw [← hcz, qCoeff_sum']
            congr 1
            exact Finset.sum_congr rfl fun g _ => (qCoeff_smul' _ _ _).symm
        _ = 0 := by rw [hr, hθrat]
    have hz0 : (∑ g ∈ t, θ (c g) • g) = 0 :=
      ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_Gamma0 N) fun n => by rw [hq n, qCoeff_zero']
    have hsum : ∑ g : b, θ (c g) • (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) = 0 := by
      rw [← Finset.sum_subtype t htb (fun g => θ (c g) • g)]
      exact hz0
    intro g hg
    have := (linearIndependent_iff'.mp hbli) Finset.univ (fun g : b => θ (c g)) hsum ⟨g, (htb g).mp hg⟩
      (Finset.mem_univ _)
    exact this

  have hcr : ∀ g ∈ t, ∃ r : ℚ, c g = (r : ℂ) := fun g hg => hθker (c g) (hθc g hg)
  choose! r hr using hcr
  refine ⟨∏ g ∈ t, (r g).den, Finset.prod_pos fun g _ => (r g).den_pos, ?_⟩
  have hkey : ∀ g ∈ t, ((∏ g' ∈ t, (r g').den : ℕ) : ℂ) * c g
      = (((r g).num * ∏ g' ∈ t.erase g, ((r g').den : ℤ) : ℤ) : ℂ) := by
    intro g hg
    rw [hr g hg, ← Finset.mul_prod_erase t (fun g' => (r g').den) hg]
    have h1 : ((r g : ℚ) : ℂ) * ((r g).den : ℂ) = ((r g).num : ℂ) := by
      have := Rat.mul_den_eq_num (r g)
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    push_cast
    calc ((r g).den : ℂ) * (∏ x ∈ t.erase g, ((r x).den : ℂ)) * (r g : ℂ)
        = ((r g : ℂ) * ((r g).den : ℂ)) * ∏ x ∈ t.erase g, ((r x).den : ℂ) := by ring
      _ = ((r g).num : ℂ) * ∏ x ∈ t.erase g, ((r x).den : ℂ) := by rw [h1]
  rw [← Int.cast_smul_eq_zsmul ℂ, ← hcz, Finset.smul_sum]
  refine Submodule.sum_mem _ fun g hg => ?_
  rw [smul_smul, Int.cast_natCast, hkey g hg, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (htL g hg)

end RatDescent

section Key

variable {M : ℕ} [NeZero M] {p : ℕ}

omit [NeZero M] in
private theorem not_dvd_R (A : ModularForm.AtkinLehnerDatum M p) (hp : p.Prime) : ¬ p ∣ A.R := by
  intro h
  have hb := A.bezout
  have h1 : (p : ℤ) ∣ (p : ℤ) * A.a - (A.R : ℤ) * A.b :=
    dvd_sub (dvd_mul_right _ _) (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h) _)
  rw [hb] at h1
  have : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1
  exact hp.one_lt.ne' this

private theorem neZero_R (A : ModularForm.AtkinLehnerDatum M p) : NeZero A.R :=
  ⟨fun h => NeZero.ne M (by rw [A.hM, h, mul_zero])⟩

private theorem qCoeff_traceLin (A : ModularForm.AtkinLehnerDatum M p) (hp : p.Prime)
    (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(traceLin A hp g)) n
      = ModularFormClass.qCoeff g n + ModularFormClass.qCoeff (⇑(atkinLehnerLin A 2 g)) (n * p) := by
  have hpM : p ∣ M := ⟨A.R, A.hM⟩
  have hcoe : (⇑(traceLin A hp g) : UpperHalfPlane → ℂ) = ⇑(g + heckeULin 2 hpM (atkinLehnerLin A 2 g)) := by
    rw [coe_traceLin_apply, CuspForm.coe_add, coe_heckeULin_apply, coe_atkinLehnerLin_apply]
  rw [hcoe, qCoeff_add', qCoeff_heckeULin' hp.ne_zero hpM]

private theorem key_coeff (A : ModularForm.AtkinLehnerDatum M p) (hp : p.Prime) [NeZero A.R]
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (n : ℕ) :
    (p : ℂ) * (if p ∣ n then ModularFormClass.qCoeff (⇑(traceLin A hp (atkinLehnerLin A 2 f))) (n / p) else 0)
      - ModularFormClass.qCoeff
          (⇑(heckeTLin 2 hp (not_dvd_R A hp) (traceLin A hp (atkinLehnerLin A 2 f)) - traceLin A hp f)) n
      = ModularFormClass.qCoeff f n - ModularFormClass.qCoeff f (n * p * p) := by
  have hT1 : ∀ m, ModularFormClass.qCoeff (⇑(traceLin A hp (atkinLehnerLin A 2 f))) m
      = ModularFormClass.qCoeff (⇑(atkinLehnerLin A 2 f)) m + ModularFormClass.qCoeff f (m * p) := by
    intro m
    rw [qCoeff_traceLin, CuspForm.atkinLehnerLin_atkinLehnerLin]
  rw [qCoeff_sub', qCoeff_heckeTLin', ModularForm.coeffHeckeT_apply, qCoeff_traceLin A hp f n,
    show (2 : ℤ) - 1 = 1 from rfl, zpow_one]
  simp only [hT1]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, if_pos hpn]
    ring
  · rw [if_neg hpn, if_neg hpn]
    ring

end Key

section Main

variable {M : ℕ} [NeZero M] (p : ℕ) [hpF : Fact p.Prime]

private theorem step {R : ℕ} [NeZero R] (hpR : ¬ p ∣ R) (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    {X T : CuspForm (CongruenceSubgroup.Gamma0 R) 2} (hX : X ∈ intLattice R 2) (hT : T ∈ intLattice R 2)
    (hredX : red ℓ X = 0) (hredY : red ℓ (heckeTLin 2 hpF.out hpR X - T) = 0) :
    ∃ X' T' : CuspForm (CongruenceSubgroup.Gamma0 R) 2, X' ∈ intLattice R 2 ∧ T' ∈ intLattice R 2 ∧
      X = (ℓ : ℤ) • X' ∧ T = (ℓ : ℤ) • T' := by
  have hY : heckeTLin 2 hpF.out hpR X - T ∈ intLattice R 2 :=
    Submodule.sub_mem _ (heckeTLin_mem_intLattice_two hpF.out hpR hX) hT
  obtain ⟨X', hX'L, hXX'⟩ := exists_eq_smul_of_red_eq_zero ℓ hℓ hX hredX
  obtain ⟨Y', hY'L, hYY'⟩ := exists_eq_smul_of_red_eq_zero ℓ hℓ hY hredY
  refine ⟨X', heckeTLin 2 hpF.out hpR X' - Y', hX'L,
    Submodule.sub_mem _ (heckeTLin_mem_intLattice_two hpF.out hpR hX'L) hY'L, hXX', ?_⟩
  have : T = heckeTLin 2 hpF.out hpR X - (heckeTLin 2 hpF.out hpR X - T) := by abel
  rw [this, hYY', hXX', map_zsmul, smul_sub]

private theorem wrow (hp2 : p ≠ 2) (A : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ intLattice M 2)
    (hrat : ∀ n : ℕ, (∃ r : ℚ, ModularFormClass.qCoeff (⇑(traceLin A hpF.out f)) n = (r : ℂ)) ∧
      (∃ r : ℚ, ModularFormClass.qCoeff (⇑(traceLin A hpF.out (atkinLehnerLin A 2 f))) n = (r : ℂ)))
    (hdesc : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ((p : ZMod ℓ) ≠ 0) → ∀ ψ : PowerSeries (ZMod ℓ),
      ψ ∈ ModPForms.modPCusp A.R 2 (ZMod ℓ) →
      (PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) ψ else 0) ∈ ModPForms.modPCusp A.R 2 (ZMod ℓ) →
      ψ = 0)
    (n : ℕ) :
    ∃ m : ℤ, (p : ℂ) * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ) := by
  classical
  haveI := neZero_R A
  have hp : p.Prime := hpF.out
  have hpR : ¬ p ∣ A.R := not_dvd_R A hp
  set x : CuspForm (CongruenceSubgroup.Gamma0 A.R) 2 := traceLin A hp (atkinLehnerLin A 2 f) with hx
  set Tf : CuspForm (CongruenceSubgroup.Gamma0 A.R) 2 := traceLin A hp f with hTf

  obtain ⟨Dx, hDx, hDxL⟩ := exists_nsmul_mem_intLattice_of_rat_qCoeff x fun m => (hrat m).2
  obtain ⟨DT, hDT, hDTL⟩ := exists_nsmul_mem_intLattice_of_rat_qCoeff Tf fun m => (hrat m).1

  have hdescent : ∀ D : ℕ, 0 < D → ((D : ℤ) • x) ∈ intLattice A.R 2 → ((D : ℤ) • Tf) ∈ intLattice A.R 2 →
      ((p : ℤ) • x) ∈ intLattice A.R 2 := by
    intro D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
    intro hD hXL hTL
    by_cases h1 : D = 1
    · subst h1
      rw [Nat.cast_one, one_smul] at hXL
      exact Submodule.smul_mem _ _ hXL
    by_cases hDp : D = p
    · subst hDp; exact hXL

    set X := (D : ℤ) • x with hXdef
    set T := (D : ℤ) • Tf with hTdef
    set Y := heckeTLin 2 hp hpR X - T with hYdef
    have hYL : Y ∈ intLattice A.R 2 := Submodule.sub_mem _ (heckeTLin_mem_intLattice_two hp hpR hXL) hTL
    have hYq : ∀ m, ModularFormClass.qCoeff Y m
        = D * ModularFormClass.qCoeff (⇑(heckeTLin 2 hp hpR x - Tf)) m := by
      intro m
      rw [hYdef, hXdef, hTdef, map_zsmul, ← smul_sub, qCoeff_zsmul']
      push_cast
      ring
    have hkeyZ : ∀ m, (p : ℤ) * (if p ∣ m then icoef X (m / p) else 0) - icoef Y m
        = D * (icoef f m - icoef f (m * p * p)) := by
      intro m
      have h := key_coeff A hp f m
      have hc : ((((p : ℤ) * (if p ∣ m then icoef X (m / p) else 0) - icoef Y m : ℤ) : ℂ))
          = (((D * (icoef f m - icoef f (m * p * p)) : ℤ) : ℂ)) := by
        push_cast
        rw [← icoef_spec hf m, ← icoef_spec hf (m * p * p), ← icoef_spec hYL m, hYq m, ← h]
        by_cases hpm : p ∣ m
        · rw [if_pos hpm, if_pos hpm, ← icoef_spec hXL (m / p), hXdef, qCoeff_zsmul']
          push_cast
          ring
        · rw [if_neg hpm, if_neg hpm]
          ring
      exact_mod_cast hc
    have hD2 : 2 ≤ D := by omega
    by_cases hA : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ D ∧ ℓ ≠ p
    ·
      obtain ⟨ℓ, hℓ, hℓD, hℓp⟩ := hA
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      have hpℓ : (p : ZMod ℓ) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)
      have hrel : (p : ZMod ℓ) • expandV p (red ℓ X) = red ℓ Y := by
        ext m
        rw [map_smul, smul_eq_mul, coeff_expandV, coeff_red, coeff_red]
        have hz := congrArg (fun z : ℤ => (z : ZMod ℓ)) (hkeyZ m)
        push_cast at hz
        rw [(ZMod.natCast_eq_zero_iff D ℓ).mpr hℓD, zero_mul, sub_eq_zero] at hz
        rw [← hz]
      have hVmem : expandV p (red ℓ X) ∈ ModPForms.modPCusp A.R 2 (ZMod ℓ) := by
        have : expandV p (red ℓ X) = (p : ZMod ℓ)⁻¹ • red ℓ Y := by
          rw [← hrel, smul_smul, inv_mul_cancel₀ hpℓ, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (red_mem_modPCusp ℓ hYL)
      have hredX : red ℓ X = 0 := hdesc ℓ hpℓ (red ℓ X) (red_mem_modPCusp ℓ hXL) hVmem
      have hredY : red ℓ Y = 0 := by
        rw [← hrel, hredX]
        ext m
        simp [coeff_expandV]
      obtain ⟨X', T', hX'L, hT'L, hXX', hTT'⟩ := step p hpR ℓ hℓ.ne_zero hXL hTL hredX hredY
      have hℓD' : D = ℓ * (D / ℓ) := (Nat.mul_div_cancel' hℓD).symm
      have hlt : D / ℓ < D := Nat.div_lt_self hD hℓ.one_lt
      have hpos : 0 < D / ℓ := Nat.div_pos (Nat.le_of_dvd hD hℓD) hℓ.pos
      have hℓC : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
      have hcancel : ∀ (u v : CuspForm (CongruenceSubgroup.Gamma0 A.R) 2),
          (D : ℤ) • u = (ℓ : ℤ) • v → ((D / ℓ : ℕ) : ℤ) • u = v := by
        intro u v huv
        apply smul_right_injective (CuspForm (CongruenceSubgroup.Gamma0 A.R) 2) hℓC
        show (ℓ : ℂ) • (((D / ℓ : ℕ) : ℤ) • u) = (ℓ : ℂ) • v
        have hv : (ℓ : ℂ) • v = (((ℓ : ℤ) : ℂ)) • v := by rw [Int.cast_natCast]
        rw [hv, Int.cast_smul_eq_zsmul, ← huv, ← Int.cast_smul_eq_zsmul ℂ ((D / ℓ : ℕ) : ℤ) u, smul_smul,
          ← Int.cast_smul_eq_zsmul ℂ (D : ℤ) u]
        congr 1
        have hnat : ((D : ℕ) : ℂ) = (ℓ : ℂ) * ((D / ℓ : ℕ) : ℂ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) hℓD'
        rw [Int.cast_natCast, Int.cast_natCast]
        exact hnat.symm
      exact ih (D / ℓ) hlt hpos (by rw [hcancel x X' hXX']; exact hX'L) (by rw [hcancel Tf T' hTT']; exact hT'L)
    ·
      push Not at hA
      have hpD : p ∣ D := by
        have h := hA (Nat.minFac D) (Nat.minFac_prime (by omega)) (Nat.minFac_dvd D)
        rw [← h]; exact Nat.minFac_dvd D
      obtain ⟨D', hDD'⟩ := hpD
      have hD'2 : 2 ≤ D' := by
        rcases Nat.lt_or_ge D' 2 with hlt | hge
        · interval_cases D'
          · omega
          · exact absurd (by rw [hDD', mul_one]) hDp
        · exact hge
      have hpD' : p ∣ D' := by
        have hmf := Nat.minFac_prime (show D' ≠ 1 by omega)
        have h := hA (Nat.minFac D') hmf ((Nat.minFac_dvd D').trans (Dvd.intro_left p hDD'.symm))
        rw [← h]; exact Nat.minFac_dvd D'

      have hredY : red p Y = 0 := by
        ext m
        rw [coeff_red, map_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
        have h := hkeyZ m
        have h1 : (p : ℤ) ∣ (D : ℤ) * (icoef f m - icoef f (m * p * p)) :=
          Dvd.dvd.mul_right (by rw [hDD']; push_cast; exact dvd_mul_right _ _) _
        rw [← h] at h1
        have h2 : (p : ℤ) ∣ (p : ℤ) * (if p ∣ m then icoef X (m / p) else 0) := dvd_mul_right _ _
        have := dvd_sub h2 h1
        rwa [sub_sub_cancel] at this
      obtain ⟨Y', hY'L, hYY'⟩ := exists_eq_smul_of_red_eq_zero p hp.ne_zero hYL hredY

      have hkeyZ' : ∀ m, (if p ∣ m then icoef X (m / p) else 0) - icoef Y' m
          = D' * (icoef f m - icoef f (m * p * p)) := by
        intro m
        have h := hkeyZ m
        have hYm : icoef Y m = p * icoef Y' m := by
          have h1 : ((icoef Y m : ℤ) : ℂ) = ((p * icoef Y' m : ℤ) : ℂ) := by
            rw [← icoef_spec hYL, hYY', qCoeff_zsmul', icoef_spec hY'L]
            push_cast
            ring
          exact_mod_cast h1
        rw [hYm, hDD'] at h
        push_cast at h
        have h' : (p : ℤ) * ((if p ∣ m then icoef X (m / p) else 0) - icoef Y' m)
            = (p : ℤ) * (D' * (icoef f m - icoef f (m * p * p))) := by rw [mul_sub, ← mul_assoc]; exact h
        exact Int.eq_of_mul_eq_mul_left (by exact_mod_cast hp.ne_zero) h'
      have hrel : expandV p (red p X) = red p Y' := by
        ext m
        rw [coeff_expandV, coeff_red, coeff_red]
        have hz := congrArg (fun z : ℤ => (z : ZMod p)) (hkeyZ' m)
        push_cast at hz
        rw [(ZMod.natCast_eq_zero_iff D' p).mpr hpD', zero_mul, sub_eq_zero] at hz
        rw [← hz]
      have hredY' : red p Y' = 0 :=
        eq_zero_of_expandV_eq_of_mem_modPCusp A.R p hp2 hpR (red p X) (red_mem_modPCusp p hY'L) hrel
      have hredX : red p X = 0 := eq_zero_of_expandV_eq_zero hp.pos (hrel.trans hredY')
      obtain ⟨X', T', hX'L, hT'L, hXX', hTT'⟩ := step p hpR p hp.ne_zero hXL hTL hredX hredY
      have hlt : D' < D := by
        rw [hDD']
        exact lt_mul_of_one_lt_left (by omega) hp.one_lt
      have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hcancel : ∀ (u v : CuspForm (CongruenceSubgroup.Gamma0 A.R) 2),
          (D : ℤ) • u = (p : ℤ) • v → ((D' : ℕ) : ℤ) • u = v := by
        intro u v huv
        apply smul_right_injective (CuspForm (CongruenceSubgroup.Gamma0 A.R) 2) hpC
        show (p : ℂ) • (((D' : ℕ) : ℤ) • u) = (p : ℂ) • v
        have hv : (p : ℂ) • v = (((p : ℤ) : ℂ)) • v := by rw [Int.cast_natCast]
        rw [hv, Int.cast_smul_eq_zsmul, ← huv, ← Int.cast_smul_eq_zsmul ℂ ((D' : ℕ) : ℤ) u, smul_smul,
          ← Int.cast_smul_eq_zsmul ℂ (D : ℤ) u]
        congr 1
        have hnat : ((D : ℕ) : ℂ) = (p : ℂ) * ((D' : ℕ) : ℂ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) hDD'
        rw [Int.cast_natCast, Int.cast_natCast]
        exact hnat.symm
      exact ih D' hlt (by omega) (by rw [hcancel x X' hXX']; exact hX'L) (by rw [hcancel Tf T' hTT']; exact hT'L)

  have hpx : ((p : ℤ) • x) ∈ intLattice A.R 2 := by
    refine hdescent (Dx * DT) (Nat.mul_pos hDx hDT) ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hDxL
    · rw [Nat.cast_mul, mul_smul]
      exact Submodule.smul_mem _ _ hDTL

  obtain ⟨a, ha⟩ := exists_int_qCoeff_of_mem_intLattice hpx n
  obtain ⟨b, hb⟩ := exists_int_qCoeff_of_mem_intLattice hf (n * p)
  have hT1 : ModularFormClass.qCoeff (⇑x) n
      = ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n + ModularFormClass.qCoeff f (n * p) := by
    rw [hx, qCoeff_traceLin, CuspForm.atkinLehnerLin_atkinLehnerLin, coe_atkinLehnerLin_apply]
  refine ⟨a - p * b, ?_⟩
  rw [qCoeff_zsmul', hT1] at ha
  push_cast at ha ⊢
  linear_combination ha - (p : ℂ) * hb

end Main

end CuspFormAlSlashDenomAux

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2) (n : ℕ) :
    ∃ m : ℤ, (p : ℂ) * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ) :=
  CuspFormAlSlashDenomAux.wrow p hp2 A f hf
    (fun m => CuspForm.exists_ratCast_qCoeff_traceLin_of_forall_intCast_qCoeff A Fact.out f
      (fun j => CuspFormAlSlashDenomAux.exists_int_qCoeff_of_mem_intLattice hf j) m)
    (fun ℓ _ hpℓ ψ hψ hV => ModPForms.eq_zero_of_mem_modPCusp_of_expand_mem_modPCusp p Fact.out A.R
      (CuspFormAlSlashDenomAux.not_dvd_R A Fact.out) 2 (ZMod ℓ) hpℓ ψ hψ hV) n

end

end S_CuspForm_exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two
end P2MW
export P2MW.S_CuspForm_exists_int_mul_qCoeff_alSlash_of_mem_intLattice_of_ne_two (solution)

-- Prove2me | solution 1 for CuspForm.exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/75e912fb-6bec-514d-ae60-e474ff20efa4

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion"
p2m_attr_erase "instance" "AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

open ModularForm Complex
p2m_open "UpperHalfPlane~I"

namespace W5O

namespace QExp

local notation "𝕢" => Function.Periodic.qParam

lemma sum_range_rootOfUnity_pow {p : ℕ} (hp : p ≠ 0) (m : ℕ) :
    ∑ j ∈ Finset.range p, (cexp (2 * Real.pi * I / p) ^ m) ^ j
      = if p ∣ m then (p : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (cexp (2 * Real.pi * I / p)) p := Complex.isPrimitiveRoot_exp p hp
  split_ifs with hdvd
  · have h1 : cexp (2 * Real.pi * I / p) ^ m = 1 := (hζ.pow_eq_one_iff_dvd m).mpr hdvd
    simp [h1]
  · have h1 : cexp (2 * Real.pi * I / p) ^ m ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd m).mp h)
    rw [geom_sum_eq h1, pow_right_comm, hζ.pow_eq_one, one_pow, sub_self, zero_div]

lemma qParam_heckeMatrix_pow {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) (m : ℕ) :
    𝕢 1 ((heckeMatrix p j • τ : ℍ) : ℂ) ^ m
      = cexp (2 * Real.pi * I * τ * m / p) * (cexp (2 * Real.pi * I / p) ^ m) ^ j := by
  rw [coe_heckeMatrix_smul hp j τ]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul, ← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma qParam_one_pow (τ : ℍ) (n : ℕ) :
    𝕢 1 (τ : ℂ) ^ n = cexp (2 * Real.pi * I * τ * n) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem hasSum_heckeU {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) (k : ℤ) {p : ℕ} (hp : p ≠ 0)
    (τ : ℍ) :
    HasSum (fun n ↦ a (n * p) * 𝕢 1 τ ^ n) (heckeU k p F τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  set ζ : ℂ := cexp (2 * Real.pi * I / p) with hζdef
  set X : ℕ → ℂ := fun m ↦ cexp (2 * Real.pi * I * τ * m / p) with hXdef
  have h1 : ∀ j ∈ Finset.range p,
      HasSum (fun m ↦ a m * (X m * (ζ ^ m) ^ j)) (F (heckeMatrix p j • τ)) := by
    intro j _
    have := hF (heckeMatrix p j • τ)
    simpa only [qParam_heckeMatrix_pow hp j τ] using this
  have h2 : HasSum (fun m ↦ ∑ j ∈ Finset.range p, a m * (X m * (ζ ^ m) ^ j))
      (∑ j ∈ Finset.range p, F (heckeMatrix p j • τ)) := hasSum_sum h1
  have h3 : (fun m ↦ ∑ j ∈ Finset.range p, a m * (X m * (ζ ^ m) ^ j))
      = fun m ↦ a m * X m * (if p ∣ m then (p : ℂ) else 0) := by
    funext m
    rw [← sum_range_rootOfUnity_pow hp m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h3] at h2
  have h4 := h2.mul_left ((p : ℂ)⁻¹)
  rw [← heckeU_apply k hp F τ] at h4
  have hinj : Function.Injective (fun n : ℕ ↦ n * p) := mul_left_injective₀ hp
  have hvan : ∀ m ∉ Set.range (fun n : ℕ ↦ n * p),
      (fun m ↦ (p : ℂ)⁻¹ * (a m * X m * (if p ∣ m then (p : ℂ) else 0))) m = 0 := by
    intro m hm
    have hndvd : ¬ p ∣ m := by
      rintro ⟨c, rfl⟩
      exact hm ⟨c, by simp [mul_comm]⟩
    simp [hndvd]
  have h5 := (hinj.hasSum_iff hvan).mpr h4
  convert h5 using 1
  funext n
  simp only [Function.comp_apply, Dvd.intro_left n rfl, if_true, hXdef]
  rw [qParam_one_pow, Nat.cast_mul, mul_div_assoc, mul_div_cancel_right₀ _ hp']
  field_simp

theorem hasSum_heckeDiag {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    HasSum (fun n ↦ (if p ∣ n then a (n / p) else 0) * 𝕢 1 τ ^ n) (F (heckeDiagMatrix p • τ)) := by
  have hinj : Function.Injective (fun n : ℕ ↦ n * p) := mul_left_injective₀ hp
  have hvan : ∀ m ∉ Set.range (fun n : ℕ ↦ n * p),
      (fun n ↦ (if p ∣ n then a (n / p) else 0) * 𝕢 1 τ ^ n) m = 0 := by
    intro m hm
    have hndvd : ¬ p ∣ m := by
      rintro ⟨c, rfl⟩
      exact hm ⟨c, by simp [mul_comm]⟩
    simp [hndvd]
  refine (hinj.hasSum_iff hvan).mp ?_
  convert hF (heckeDiagMatrix p • τ) using 1
  funext m
  simp only [Function.comp_apply, Dvd.intro_left m rfl, if_true, Nat.mul_div_cancel _
    (Nat.pos_of_ne_zero hp)]
  congr 1
  rw [coe_heckeDiagMatrix_smul hp τ, qParam_one_pow]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem hasSum_heckeT {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) (k : ℤ) {p : ℕ} (hp : p ≠ 0)
    (τ : ℍ) :
    HasSum (fun n ↦ coeffHeckeT k p a n * 𝕢 1 τ ^ n) (heckeT k p F τ) := by
  have hU := hasSum_heckeU hF k hp τ
  have hD := (hasSum_heckeDiag hF hp τ).mul_left ((p : ℂ) ^ (k - 1))
  rw [heckeT, Pi.add_apply, slash_heckeDiagMatrix_apply k hp]
  convert hU.add hD using 1
  funext n
  rw [coeffHeckeT_apply]
  split_ifs <;> ring

lemma one_mem_strictPeriods_gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

lemma hasSum_qCoeff {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m ↦ ModularFormClass.qCoeff f m * 𝕢 1 τ ^ m) (f τ) := by
  have h1 := one_mem_strictPeriods_gamma0 N
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f h1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  simp only [smul_eq_mul] at this
  exact this

lemma qCoeff_unique {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) {c : ℕ → ℂ}
    (hc : ∀ τ : ℍ, HasSum (fun m ↦ c m * 𝕢 1 τ ^ m) (f τ)) (n : ℕ) :
    ModularFormClass.qCoeff f n = c n := by
  have h1 := one_mem_strictPeriods_gamma0 N
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have han : AnalyticAt ℂ (cuspFunction 1 f) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f one_pos h1
  have hc' : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 1 τ ^ m) (f τ) := by
    simpa only [smul_eq_mul] using hc
  exact (qExpansion_coeff_unique _ one_pos han hc' n).symm

theorem eq_of_qCoeff_eq {N : ℕ} {k : ℤ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (h : ∀ n, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by
  refine DFunLike.ext _ _ fun τ => ?_
  have hf := hasSum_qCoeff f τ
  have hg := hasSum_qCoeff g τ
  simp_rw [h] at hf
  exact hf.unique hg

theorem qCoeff_add {N : ℕ} {k : ℤ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n = ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n := by
  refine qCoeff_unique (f + g)
    (c := fun m => ModularFormClass.qCoeff f m + ModularFormClass.qCoeff g m) (fun τ => ?_) n
  have := (hasSum_qCoeff f τ).add (hasSum_qCoeff g τ)
  simpa only [add_mul, CuspForm.add_apply] using this

theorem qCoeff_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) n = c * ModularFormClass.qCoeff f n := by
  refine qCoeff_unique (c • f) (c := fun m => c * ModularFormClass.qCoeff f m) (fun τ => ?_) n
  have := (hasSum_qCoeff f τ).mul_left c
  simpa only [mul_assoc, CuspForm.smul_apply, smul_eq_mul] using this

noncomputable def qCoeffLin (N : ℕ) (k : ℤ) (n : ℕ) : CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff f n
  map_add' f g := qCoeff_add f g n
  map_smul' c f := qCoeff_smul c f n

@[scoped simp] theorem qCoeffLin_apply (N : ℕ) (k : ℤ) (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    qCoeffLin N k n f = ModularFormClass.qCoeff f n := rfl

theorem qCoeff_heckeTLin {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLin k hp hpN f) n =
      coeffHeckeT k p (fun m ↦ ModularFormClass.qCoeff f m) n := by
  refine qCoeff_unique _ (c := coeffHeckeT k p (fun m ↦ ModularFormClass.qCoeff f m)) (fun τ => ?_) n
  simpa only [CuspForm.heckeTLin_apply_apply] using hasSum_heckeT (hasSum_qCoeff f) k hp.ne_zero τ

theorem qCoeff_heckeULin {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    {p : ℕ} (hpN : p ∣ N) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin k hpN f) n = ModularFormClass.qCoeff f (n * p) := by
  have hp : p ≠ 0 := by
    rintro rfl
    exact (NeZero.ne N) (zero_dvd_iff.mp hpN)
  refine qCoeff_unique _ (c := fun m => ModularFormClass.qCoeff f (m * p)) (fun τ => ?_) n
  simpa only [CuspForm.heckeULin_apply_apply] using hasSum_heckeU (hasSum_qCoeff f) k hp τ

end QExp
p2m_reactivate "P2MW.S_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast.W5O.QExp"

section Rational

variable {N : ℕ}

def intSet (N : ℕ) : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  {f | ∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff f n = (m : ℂ)}

def IsRat (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop :=
  ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ Set.range ((↑) : ℚ → ℂ)

theorem isRat_of_mem_intSet {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f ∈ intSet N) :
    IsRat f := fun n => by
  obtain ⟨m, hm⟩ := hf n
  exact ⟨m, by rw [hm]; push_cast; rfl⟩

theorem isRat_heckeTLin {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : IsRat f)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : IsRat (CuspForm.heckeTLin 2 hℓ hℓN f) := by
  intro n
  choose a ha using hf
  rw [QExp.qCoeff_heckeTLin f hℓ hℓN n, coeffHeckeT_apply]
  have h2 : ((ℓ : ℂ)) ^ ((2 : ℤ) - 1) = (ℓ : ℚ) := by norm_num
  by_cases hdvd : ℓ ∣ n
  · refine ⟨a (n * ℓ) + ℓ * a (n / ℓ), ?_⟩
    rw [if_pos hdvd, h2, ← ha, ← ha]; push_cast; ring
  · refine ⟨a (n * ℓ), ?_⟩
    rw [if_neg hdvd, ← ha, add_zero]

theorem isRat_heckeULin [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : IsRat f)
    {q : ℕ} (hqN : q ∣ N) : IsRat (CuspForm.heckeULin 2 hqN f) := by
  intro n
  rw [QExp.qCoeff_heckeULin f hqN n]
  exact hf (n * q)

theorem repr_mem_range_ratCast {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) (hb : ∀ i, IsRat (b i))
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : IsRat g) (j : ι) :
    b.repr g j ∈ Set.range ((↑) : ℚ → ℂ) := by
  classical

  obtain ⟨r, hr⟩ : ∃ r : ℂ →ₗ[ℚ] ℚ, r.comp (Algebra.linearMap ℚ ℂ) = LinearMap.id :=
    LinearMap.exists_leftInverse_of_injective _
      (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
  have hr' : ∀ q : ℚ, r (q : ℂ) = q := fun q => by
    simpa using LinearMap.congr_fun hr q

  choose β hβ using fun i n => hb i n
  choose γ hγ using hg
  set x : ι → ℂ := fun i => b.repr g i with hx

  set g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2 := ∑ i, ((r (x i) : ℚ) : ℂ) • b i with hg'
  have hsum : ∑ i, x i • b i = g := b.sum_repr g

  have hcoef : ∀ n, (γ n : ℂ) = ∑ i, x i * (β i n : ℂ) := fun n => by
    have := congrArg (fun f => QExp.qCoeffLin N 2 n f) hsum
    simp only [map_sum, map_smul, smul_eq_mul, QExp.qCoeffLin_apply] at this
    rw [hγ, ← this]
    exact Finset.sum_congr rfl fun i _ => by rw [hβ]

  have hrat : ∀ n, γ n = ∑ i, β i n * r (x i) := fun n => by
    have h := congrArg r (hcoef n)
    rw [hr', map_sum] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : x i * (β i n : ℂ) = (β i n) • x i := by rw [Rat.smul_def, mul_comm]
    rw [this, map_smul, smul_eq_mul]

  have hg'g : g' = g := by
    refine QExp.eq_of_qCoeff_eq _ _ fun n => ?_
    have := map_sum (QExp.qCoeffLin N 2 n) (fun i => ((r (x i) : ℚ) : ℂ) • b i) Finset.univ
    simp only [map_smul, smul_eq_mul, QExp.qCoeffLin_apply] at this
    rw [hg', this, ← hγ, hrat n]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [← hβ]; ring

  have hrepr : b.repr g' j = ((r (x j) : ℚ) : ℂ) := by
    rw [hg']
    have := b.repr_sum_self (fun i => ((r (x i) : ℚ) : ℂ))
    exact congrFun this j
  refine ⟨r (x j), ?_⟩
  rw [← hrepr, hg'g]

end Rational
p2m_reactivate "P2MW.S_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast.W5O.QExp"

theorem main (N : ℕ) [NeZero N] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i j : Fin n),
          b.repr (CuspForm.heckeTLin 2 hℓ hℓN (b i)) j ∈ Set.range ((↑) : ℚ → ℂ)) ∧
        (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (i j : Fin n),
          b.repr (CuspForm.heckeULin 2 hqN (b i)) j ∈ Set.range ((↑) : ℚ → ℂ)) := by
  classical
  haveI : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    CuspForm.finiteDimensional_Gamma0 N 2

  have hspan : Submodule.span ℂ (intSet N) = ⊤ := by
    have h := CuspForm.hasIntegralStructure_two N
    unfold CuspForm.HasIntegralStructure CuspForm.intLattice at h
    rwa [Submodule.span_span_of_tower] at h

  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent ℂ (intSet N)
  have hBfin : B.Finite := hBli.set_finite_of_isNoetherian
  haveI : Fintype B := hBfin.fintype
  have hBtop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : B → CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by
    rw [Subtype.range_coe, hBspan, hspan]
  let b₀ : Module.Basis B ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := Module.Basis.mk hBli hBtop
  let e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let b : Module.Basis (Fin (Fintype.card B)) ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    b₀.reindex e
  have hb : ∀ i, IsRat (b i) := fun i => by
    have : b i = ((e.symm i : B) : CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
      simp [b, b₀, Module.Basis.reindex_apply, Module.Basis.mk_apply]
    rw [this]
    exact isRat_of_mem_intSet (hBsub (e.symm i).2)
  refine ⟨Fintype.card B, b, fun ℓ hℓ hℓN i j => ?_, fun q _ hqN i j => ?_⟩
  · exact repr_mem_range_ratCast b hb (isRat_heckeTLin (hb i) hℓ hℓN) j
  · exact repr_mem_range_ratCast b hb (isRat_heckeULin (hb i) hqN) j

end W5O
p2m_reactivate "P2MW.S_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast.W5O.QExp P2MW.S_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast.W5O"

theorem solution (N : ℕ) [NeZero N] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i j : Fin n),
          b.repr (CuspForm.heckeTLin 2 hℓ hℓN (b i)) j ∈ Set.range ((↑) : ℚ → ℂ)) ∧
        (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (i j : Fin n),
          b.repr (CuspForm.heckeULin 2 hqN (b i)) j ∈ Set.range ((↑) : ℚ → ℂ)) :=
  W5O.main N

end S_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast
end P2MW
export P2MW.S_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast (solution)

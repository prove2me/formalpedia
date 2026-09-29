-- Prove2me | solution 1 for CohCarrier.exists_ringHom_heckeAlgebra_and_forall_exists_eigenclass_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d4a4a6c4-68ae-5a64-88f7-ccfc2203b84c

import Theorems.Thm_CohCarrier_exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Definitions.Def_CohCarrier_Inst
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_ringHom_heckeAlgebra_and_forall_exists_eigenclass_of_ker_eq
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe"
p2m_attr_erase "simp" "ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open CohCarrier ModularCurve.Period CuspForm

namespace DescSol

theorem heckeAlgebra_induction' (N' : ℕ) [NeZero N'] (S : Set ℕ)
    {R : Type} [Ring R] (F : heckeAlgebra N' 2 S →+* R) (B : Subring R)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN' : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S),
      F (heckeAlgebra.T hℓ hℓN' hℓS) ∈ B)
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqN' : q ∣ N') (hqS : q ∉ S),
      F (heckeAlgebra.U hq hqN' hqS) ∈ B)
    (t : heckeAlgebra N' 2 S) : F t ∈ B := by
  classical
  obtain ⟨t, ht⟩ := t
  refine Algebra.adjoin_induction (p := fun t ht => F ⟨t, ht⟩ ∈ B) ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, hℓ, hℓN', hℓS, rfl⟩ | ⟨q, hqN', hq, hqS, rfl⟩)
    · exact hT ℓ hℓ hℓN' hℓS
    · exact hU q hq hqN' hqS
  · intro r
    have e : (⟨algebraMap ℤ _ r, algebraMap_mem _ r⟩ : heckeAlgebra N' 2 S) =
        (r : heckeAlgebra N' 2 S) := Subtype.ext (by simp)
    rw [e, map_intCast F r]
    exact intCast_mem _ r
  · intro x y hx hy hpx hpy
    have e : (⟨x + y, add_mem hx hy⟩ : heckeAlgebra N' 2 S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, RingHom.map_add]
    exact add_mem hpx hpy
  · intro x y hx hy hpx hpy
    have e : (⟨x * y, mul_mem hx hy⟩ : heckeAlgebra N' 2 S) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [e, RingHom.map_mul]
    exact mul_mem hpx hpy

section Transport

variable (M : ℕ) (F : Type) [Field F]

abbrev PZ : Type := ↥(parabolicHoms ℤ (GammaH M ⊤) ℤ)
abbrev PF : Type := ↥(parabolicHoms F (GammaH M ⊤) F)

private def _root_.DescSol.ext : H1 M ⊤ ℤ →ₗ[ℤ] H1 M ⊤ F where
  toFun φ := (Int.castAddHom F).comp φ
  map_add' φ ψ := by ext; simp
  map_smul' n φ := by ext; simp

p2m_export "DescSol" "ext"
theorem ext_apply (φ : H1 M ⊤ ℤ) : ext M F φ = (Int.castAddHom F).comp φ := rfl

theorem ext_mem {φ : H1 M ⊤ ℤ} (hφ : φ ∈ parabolicHoms ℤ (GammaH M ⊤) ℤ) :
    ext M F φ ∈ parabolicHoms F (GammaH M ⊤) F := by
  rw [mem_parabolicHoms_iff] at hφ ⊢
  intro γ hγ
  rw [ext_apply, AddMonoidHom.comp_apply, hφ γ hγ, map_zero]

def extP : PZ M →ₗ[ℤ] PF M F where
  toFun φ := ⟨ext M F φ, ext_mem M F φ.2⟩
  map_add' φ ψ := Subtype.ext (by simp)
  map_smul' n φ := Subtype.ext (by simp)

theorem coe_extP (φ : PZ M) : (extP M F φ : H1 M ⊤ F) = (Int.castAddHom F).comp (φ : H1 M ⊤ ℤ) := rfl

theorem heckeT_ext (ℓ : ℕ) [NeZero ℓ] (φ : H1 M ⊤ ℤ) :
    heckeT M ⊤ ℓ F (ext M F φ) = ext M F (heckeT M ⊤ ℓ ℤ φ) :=
  heckeT_comp_coeff M ⊤ ℓ (Int.castAddHom F) φ

variable {M F}
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (PZ M)) (bF : Module.Basis (Fin n) F (PF M F))
  (hb : ∀ i, (bF i : H1 M ⊤ F) = (Int.castAddHom F).comp (b i : H1 M ⊤ ℤ))

include hb in
theorem extP_basis (i : Fin n) : extP M F (b i) = bF i := Subtype.ext (by rw [coe_extP, hb])

def ιF : Module.End ℤ (PZ M) →+* Module.End F (PF M F) :=
  ((Matrix.toLinAlgEquiv bF).toRingEquiv.toRingHom.comp (Int.castRingHom F).mapMatrix).comp
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom

theorem ιF_apply (f : Module.End ℤ (PZ M)) :
    ιF b bF f = Matrix.toLin bF bF ((LinearMap.toMatrix b b f).map (Int.castRingHom F)) := rfl

theorem repr_ιF (f : Module.End ℤ (PZ M)) (x : PF M F) :
    ⇑(bF.repr (ιF b bF f x)) =
      Matrix.mulVec ((LinearMap.toMatrix b b f).map (Int.castRingHom F)) ⇑(bF.repr x) := by
  rw [ιF_apply, Matrix.repr_toLin]

include hb in
theorem ιF_extP (f : Module.End ℤ (PZ M)) (φ : PZ M) :
    ιF b bF f (extP M F φ) = extP M F (f φ) := by
  classical
  suffices h : ((ιF b bF f).restrictScalars ℤ).comp (extP M F) = (extP M F).comp f from
    LinearMap.congr_fun h φ
  refine b.ext fun j => ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [extP_basis b bF hb j, ιF_apply, Matrix.toLin_self]
  conv_rhs => rw [← b.sum_repr (f (b j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, Int.coe_castRingHom, map_zsmul,
    extP_basis b bF hb i, Int.cast_smul_eq_zsmul]

end Transport

section Point

variable {R V : Type} [Ring R] {F : Type} [Field F] [AddCommGroup V] [Module F V]

def eigSubring (v : V) : Subring (Module.End F V) where
  carrier := {g | ∃ a : F, g v = a • v}
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a' * a, by rw [Module.End.mul_apply, ha', map_smul, ha, smul_smul]⟩
  one_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro g h ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [LinearMap.add_apply, ha, ha', add_smul]⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro g ⟨a, ha⟩
    exact ⟨-a, by rw [LinearMap.neg_apply, ha, neg_smul]⟩

theorem exists_ringHom_of_forall_exists_smul (ρ : R →+* Module.End F V) (v : V) (hv : v ≠ 0)
    (h : ∀ t, ∃ a : F, ρ t v = a • v) :
    ∃ χ : R →+* F, ∀ t, ρ t v = χ t • v := by
  classical
  choose a ha using h
  have huniq : ∀ {x y : F}, x • v = y • v → x = y := fun hxy => smul_left_injective F hv hxy
  refine ⟨{ toFun := a, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ha⟩
  · apply huniq; rw [← ha 1, map_one, one_smul]; rfl
  · intro s t
    apply huniq
    rw [← ha (s * t), map_mul, Module.End.mul_apply, ha t, map_smul, ha s, smul_smul, mul_comm]
  · apply huniq; rw [← ha 0, map_zero, zero_smul]; rfl
  · intro s t
    apply huniq
    rw [← ha (s + t), map_add, LinearMap.add_apply, ha s, ha t, add_smul]

end Point

section Action

variable (M : ℕ) [NeZero M] (S : Set ℕ)
  (ρ : ↥(heckeAlgebra M 2 S) →+* Module.End ℤ (PZ M))
  {n : ℕ} (b : Module.Basis (Fin n) ℤ (PZ M))
  (K : Type) [Field K] (bK : Module.Basis (Fin n) K (PF M K))
  (hbK : ∀ i, (bK i : H1 M ⊤ K) = (Int.castAddHom K).comp (b i : H1 M ⊤ ℤ))

include hbK in

theorem ρK_eq_heckeT (t : heckeAlgebra M 2 S) (ℓ : ℕ) [NeZero ℓ]
    (ht : ∀ φ : PZ M, ((ρ t φ : PZ M) : H1 M ⊤ ℤ) = heckeT M ⊤ ℓ ℤ φ) (ψ : PF M K) :
    (((ιF b bK).comp ρ t ψ : PF M K) : H1 M ⊤ K) = heckeT M ⊤ ℓ K (ψ : H1 M ⊤ K) := by
  let L : PF M K →ₗ[K] H1 M ⊤ K :=
    (parabolicHoms K (GammaH M ⊤) K).subtype.comp ((ιF b bK).comp ρ t)
  let R' : PF M K →ₗ[K] H1 M ⊤ K := (heckeTL M ⊤ K ℓ).comp (parabolicHoms K (GammaH M ⊤) K).subtype
  suffices h : L = R' from LinearMap.congr_fun h ψ
  refine bK.ext fun j => ?_
  show (((ιF b bK).comp ρ t (bK j) : PF M K) : H1 M ⊤ K) = heckeT M ⊤ ℓ K (bK j : H1 M ⊤ K)
  rw [RingHom.comp_apply, ← extP_basis b bK hbK j, ιF_extP b bK hbK, coe_extP, coe_extP, ht (b j)]
  exact (heckeT_ext M K ℓ (b j : H1 M ⊤ ℤ)).symm

end Action

end DescSol

end

open DescSol CohCarrier ModularCurve.Period CuspForm in
theorem solution
    (M : ℕ) [NeZero M] (S : Set ℕ)
    (F : Type) [Field F] [CharZero F]
    (c : CohCarrier.H1 M ⊤ F)
    (hc : c ∈ ModularCurve.Period.parabolicHoms F (CohCarrier.GammaH M ⊤) F) (hc0 : c ≠ 0)
    (a : ℕ → F)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M ⊤ ℓ F c) = a ℓ • c) :
    ∃ χ : CuspForm.heckeAlgebra M 2 S →+* F,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ S),
        χ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = a ℓ) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqS : q ∉ S),
        χ (CuspForm.heckeAlgebra.U hq hqM hqS) = a q) ∧
      ∀ (K : Type) [Field K] [CharZero K] (ψ : CuspForm.heckeAlgebra M 2 S →+* K),
        (∀ t, χ t = 0 ↔ ψ t = 0) →
        ∃ c' : CohCarrier.H1 M ⊤ K,
          c' ∈ ModularCurve.Period.parabolicHoms K (CohCarrier.GammaH M ⊤) K ∧ c' ≠ 0 ∧
          (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ S),
            (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M ⊤ ℓ K c') =
              ψ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) • c') ∧
          (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqS : q ∉ S),
            (haveI : NeZero q := ⟨hq.ne_zero⟩; CohCarrier.heckeT M ⊤ q K c') =
              ψ (CuspForm.heckeAlgebra.U hq hqM hqS) • c') := by
  classical
  haveI : (GammaH M ⊤).FiniteIndex := by rw [GammaH_top]; infer_instance

  obtain ⟨-, ρ, -, hρT, hρU⟩ := CohCarrier.exists_injective_ringHom_heckeAlgebra_moduleEnd_parabolicHoms M S

  obtain ⟨n, b, hbF⟩ := ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (GammaH M ⊤)
  obtain ⟨bF, hb⟩ := hbF F
  set ρF : heckeAlgebra M 2 S →+* Module.End F (PF M F) := (ιF b bF).comp ρ with hρFdef
  set cF : PF M F := ⟨c, hc⟩ with hcFdef
  have hcF0 : cF ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  have hρFT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ S) (ψ : PF M F),
      ((ρF (heckeAlgebra.T hℓ hℓM hℓS) ψ : PF M F) : H1 M ⊤ F) =
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT M ⊤ ℓ F (ψ : H1 M ⊤ F)) := by
    intro ℓ hℓ hℓM hℓS ψ
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact ρK_eq_heckeT M S ρ b F bF hb _ ℓ (hρT ℓ hℓ hℓM hℓS) ψ
  have hρFU : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqS : q ∉ S) (ψ : PF M F),
      ((ρF (heckeAlgebra.U hq hqM hqS) ψ : PF M F) : H1 M ⊤ F) =
        (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT M ⊤ q F (ψ : H1 M ⊤ F)) := by
    intro q hq hqM hqS ψ
    haveI : NeZero q := ⟨hq.ne_zero⟩
    exact ρK_eq_heckeT M S ρ b F bF hb _ q (hρU q hq hqM hqS) ψ

  have hall : ∀ t : heckeAlgebra M 2 S, ∃ a' : F, ρF t cF = a' • cF := by
    intro t
    refine heckeAlgebra_induction' M S ρF (eigSubring cF) ?_ ?_ t
    · intro ℓ hℓ hℓM hℓS
      refine ⟨a ℓ, Subtype.ext ?_⟩
      rw [hρFT ℓ hℓ hℓM hℓS cF]
      exact heig ℓ hℓ hℓS
    · intro q hq hqM hqS
      refine ⟨a q, Subtype.ext ?_⟩
      rw [hρFU q hq hqM hqS cF]
      exact heig q hq hqS
  obtain ⟨χ, hχ⟩ := exists_ringHom_of_forall_exists_smul ρF cF hcF0 hall
  have huniq : ∀ {x y : F}, x • cF = y • cF → x = y := fun hxy => smul_left_injective F hcF0 hxy
  have hχT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ S),
      χ (heckeAlgebra.T hℓ hℓM hℓS) = a ℓ := by
    intro ℓ hℓ hℓM hℓS
    apply huniq
    apply Subtype.ext
    rw [← hχ (heckeAlgebra.T hℓ hℓM hℓS), hρFT ℓ hℓ hℓM hℓS cF]
    exact heig ℓ hℓ hℓS
  have hχU : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqS : q ∉ S),
      χ (heckeAlgebra.U hq hqM hqS) = a q := by
    intro q hq hqM hqS
    apply huniq
    apply Subtype.ext
    rw [← hχ (heckeAlgebra.U hq hqM hqS), hρFU q hq hqM hqS cF]
    exact heig q hq hqS
  refine ⟨χ, hχT, hχU, ?_⟩

  intro K _ _ ψ hker
  obtain ⟨bK, hbK⟩ := hbF K
  set ρK : heckeAlgebra M 2 S →+* Module.End K (PF M K) := (ιF b bK).comp ρ with hρKdef

  haveI : Module.Finite ℤ (heckeAlgebra M 2 S) := CuspForm.moduleFinite_heckeAlgebra_two M S
  obtain ⟨m, gen, hgen⟩ := Module.Finite.exists_fin (R := ℤ) (M := heckeAlgebra M 2 S)

  set A : Fin m → Matrix (Fin n) (Fin n) ℤ := fun i => LinearMap.toMatrix b b (ρ (gen i)) with hAdef

  set 𝔭 : Ideal (heckeAlgebra M 2 S) := RingHom.ker χ with h𝔭def
  set χbar : heckeAlgebra M 2 S ⧸ 𝔭 →+* F := RingHom.kerLift χ with hχbardef
  have hχbar_inj : Function.Injective χbar := RingHom.kerLift_injective χ
  have hψker : ∀ t ∈ 𝔭, ψ t = 0 := fun t ht => (hker t).mp (RingHom.mem_ker.mp ht)
  set ψbar : heckeAlgebra M 2 S ⧸ 𝔭 →+* K := Ideal.Quotient.lift 𝔭 ψ hψker with hψbardef
  have hψbar_inj : Function.Injective ψbar := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hψbardef, Ideal.Quotient.lift_mk] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr ((hker t).mpr hx))
  haveI : IsDomain (heckeAlgebra M 2 S ⧸ 𝔭) := hχbar_inj.isDomain χbar

  set v : Fin n → (Fin m × Fin n) → heckeAlgebra M 2 S ⧸ 𝔭 := fun col p =>
    Ideal.Quotient.mk 𝔭 (((A p.1 p.2 col : ℤ) : heckeAlgebra M 2 S) -
      if p.2 = col then gen p.1 else 0) with hvdef

  have key : ∀ (K' : Type) [Field K'] (bK' : Module.Basis (Fin n) K' (PF M K'))
      (θ : heckeAlgebra M 2 S →+* K') (θbar : heckeAlgebra M 2 S ⧸ 𝔭 →+* K')
      (hθ : ∀ t, θbar (Ideal.Quotient.mk 𝔭 t) = θ t) (x : PF M K'),
      (∀ i, (ιF b bK').comp ρ (gen i) x = θ (gen i) • x) ↔
        ∑ col, (bK'.repr x col) • (fun p => θbar (v col p)) = 0 := by
    intro K' _ bK' θ θbar hθ x
    have hcoord : ∀ i, ((ιF b bK').comp ρ (gen i) x = θ (gen i) • x ↔
        ∀ j, ∑ col, (bK'.repr x col) * θbar (v col (i, j)) = 0) := by
      intro i
      rw [← bK'.repr.injective.eq_iff, map_smul]
      rw [show ((bK'.repr ((ιF b bK').comp ρ (gen i) x)) = θ (gen i) • bK'.repr x) ↔
          (⇑(bK'.repr ((ιF b bK').comp ρ (gen i) x)) = ⇑(θ (gen i) • bK'.repr x)) from
        DFunLike.coe_injective.eq_iff.symm]
      rw [RingHom.comp_apply, repr_ιF, Finsupp.coe_smul, funext_iff]
      refine forall_congr' fun j => ?_
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      have e : ∑ col, (bK'.repr x col) * θbar (v col (i, j)) =
          (∑ col, ((A i).map (Int.castRingHom K')) j col * (bK'.repr x) col) - θ (gen i) * bK'.repr x j := by
        simp only [hvdef, map_sub]
        have : ∀ col, (bK'.repr x col) * (θbar (Ideal.Quotient.mk 𝔭 ((A i j col : ℤ) : heckeAlgebra M 2 S)) -
            θbar (Ideal.Quotient.mk 𝔭 (if j = col then gen i else 0))) =
            ((A i).map (Int.castRingHom K')) j col * (bK'.repr x) col -
              (if j = col then θ (gen i) * bK'.repr x j else 0) := by
          intro col
          rw [hθ, hθ, map_intCast, Matrix.map_apply, Int.coe_castRingHom]
          split_ifs with hjc
          · subst hjc; ring
          · rw [map_zero]; ring
        rw [Finset.sum_congr rfl fun col _ => this col, Finset.sum_sub_distrib, Finset.sum_ite_eq]
        simp
      rw [e, sub_eq_zero, hAdef]
    rw [funext_iff]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Prod.forall]
    exact ⟨fun h i j => (hcoord i).mp (h i) j, fun h i => (hcoord i).mpr fun j => h i j⟩

  letI algF : Algebra (heckeAlgebra M 2 S ⧸ 𝔭) F := χbar.toAlgebra
  letI algK : Algebra (heckeAlgebra M 2 S ⧸ 𝔭) K := ψbar.toAlgebra
  haveI : FaithfulSMul (heckeAlgebra M 2 S ⧸ 𝔭) F :=
    (faithfulSMul_iff_algebraMap_injective _ F).mpr hχbar_inj
  haveI : FaithfulSMul (heckeAlgebra M 2 S ⧸ 𝔭) K :=
    (faithfulSMul_iff_algebraMap_injective _ K).mpr hψbar_inj
  have hdepF : ¬ LinearIndependent F (fun col => algebraMap (heckeAlgebra M 2 S ⧸ 𝔭) F ∘ v col) := by
    rw [Fintype.not_linearIndependent_iff]
    refine ⟨fun col => bF.repr cF col, ?_, ?_⟩
    · have h := (key F bF χ χbar (fun t => RingHom.kerLift_mk χ t) cF).mp fun i => hχ (gen i)
      exact h
    · by_contra hall0
      push Not at hall0
      apply hcF0
      rw [← bF.repr.injective.eq_iff, map_zero]
      ext col
      exact hall0 col

  have hdepK : ¬ LinearIndependent K (fun col => algebraMap (heckeAlgebra M 2 S ⧸ 𝔭) K ∘ v col) := by
    rw [linearIndependent_algebraMap_comp_iff]
    rwa [linearIndependent_algebraMap_comp_iff] at hdepF
  rw [Fintype.not_linearIndependent_iff] at hdepK
  obtain ⟨ξ, hξ, col₀, hcol₀⟩ := hdepK

  set y : PF M K := ∑ col, ξ col • bK col with hydef
  have hyrepr : ∀ col, bK.repr y col = ξ col := by
    intro col
    rw [hydef, map_sum]
    simp [Finsupp.single_apply]
  have hy0 : y ≠ 0 := by
    intro h
    apply hcol₀
    rw [← hyrepr col₀, h, map_zero, Finsupp.zero_apply]
  have hygen : ∀ i, ρK (gen i) y = ψ (gen i) • y := by
    refine (key K bK ψ ψbar (fun t => Ideal.Quotient.lift_mk 𝔭 ψ hψker) y).mpr ?_
    have e : (fun col => bK.repr y col) = ξ := funext hyrepr
    simp only [hyrepr]
    exact hξ

  have hyall : ∀ t : heckeAlgebra M 2 S, ρK t y = ψ t • y := by
    intro t
    have ht : t ∈ Submodule.span ℤ (Set.range gen) := by rw [hgen]; exact Submodule.mem_top
    refine Submodule.span_induction (p := fun t _ => ρK t y = ψ t • y) ?_ ?_ ?_ ?_ ht
    · rintro _ ⟨i, rfl⟩
      exact hygen i
    · rw [map_zero, map_zero, zero_smul, LinearMap.zero_apply]
    · intro s t _ _ hs ht
      rw [map_add, map_add, LinearMap.add_apply, hs, ht, add_smul]
    · intro k t _ ht
      rw [map_zsmul, map_zsmul, LinearMap.smul_apply, ht, smul_assoc]
  refine ⟨(y : H1 M ⊤ K), y.2, fun h => hy0 (Subtype.ext h), ?_, ?_⟩
  · intro ℓ hℓ hℓM hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have h := congrArg Subtype.val (hyall (heckeAlgebra.T hℓ hℓM hℓS))
    rw [hρKdef, ρK_eq_heckeT M S ρ b K bK hbK _ ℓ (hρT ℓ hℓ hℓM hℓS) y] at h
    exact h
  · intro q hq hqM hqS
    haveI : NeZero q := ⟨hq.ne_zero⟩
    have h := congrArg Subtype.val (hyall (heckeAlgebra.U hq hqM hqS))
    rw [hρKdef, ρK_eq_heckeT M S ρ b K bK hbK _ q (hρU q hq hqM hqS) y] at h
    exact h

end S_CohCarrier_exists_ringHom_heckeAlgebra_and_forall_exists_eigenclass_of_ker_eq
end P2MW
export P2MW.S_CohCarrier_exists_ringHom_heckeAlgebra_and_forall_exists_eigenclass_of_ker_eq (solution)

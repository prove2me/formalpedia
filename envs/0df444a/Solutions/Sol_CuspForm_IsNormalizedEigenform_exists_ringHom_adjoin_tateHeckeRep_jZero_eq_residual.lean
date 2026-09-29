-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_ringHom_adjoin_tateHeckeRep_jZero_eq_residual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/02de4884-f8d7-5445-a0c5-c32a6428fa8f

import Mathlib
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_EigenformCoefficientRing
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_linearIndependent_rationalHeckeRep_of_linearIndependent
import Theorems.Thm_ModularCurve_exists_injective_ringHom_adjoin_heckeOperatorBar_cuspForm
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Theorems.Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_ringHom_adjoin_tateHeckeRep_jZero_eq_residual
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

open scoped TensorProduct

noncomputable section

namespace W7HA1

open Submodule in

theorem transfer_relation
    {R P T E Ω : Type} [CommRing R]
    [AddCommGroup P] [AddCommGroup T] [AddCommGroup E] [Module R E]
    [AddCommGroup Ω] [Module R Ω]
    (htf : ∀ (n : ℤ) (v : T), n • v = 0 → n = 0 ∨ v = 0)
    (α : P →+ T) (β : P →+ Ω) (hαβ : ∀ g, α g = 0 → β g = 0)
    (γ : T →+ E)
    (hγ : ∀ {ι : Type} (u : ι → T), LinearIndependent ℤ u → LinearIndependent R (fun i => γ (u i)))
    {κ : Type} [Fintype κ] (x : κ → P) (c : κ → R)
    (hf : ∑ k, c k • γ (α (x k)) = 0) :
    ∑ k, c k • β (x k) = 0 := by
  classical
  haveI : Module.IsTorsionFree ℤ T := Module.IsTorsionFree.of_smul_eq_zero htf

  let L : Submodule ℤ T := span ℤ (Set.range fun k => α (x k))
  haveI : Module.Finite ℤ L := Module.Finite.span_of_finite ℤ (Set.finite_range _)
  let b := Module.finBasis ℤ L
  have hbT : LinearIndependent ℤ (fun j => (b j : T)) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hγb : LinearIndependent R (fun j => γ (b j : T)) := hγ _ hbT
  have hxL : ∀ k, α (x k) ∈ L := fun k => subset_span (Set.mem_range_self k)

  let n : κ → Fin (Module.finrank ℤ L) → ℤ := fun k j => b.repr ⟨α (x k), hxL k⟩ j
  have hx : ∀ k, α (x k) = ∑ j, n k j • (b j : T) := fun k => by
    have h := congrArg Subtype.val (b.sum_repr ⟨α (x k), hxL k⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at h
    exact h.symm

  have hb_lift : ∀ j, ∃ y : P, α y = (b j : T) := fun j => by
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (b j).2
    refine ⟨∑ k, m k • x k, ?_⟩
    rw [map_sum]
    simp_rw [map_zsmul]
    exact hm
  choose y hy using hb_lift
  have hβ : ∀ k, β (x k) = ∑ j, n k j • β (y j) := fun k => by
    have h0 : α (x k - ∑ j, n k j • y j) = 0 := by
      rw [map_sub, map_sum]
      simp_rw [map_zsmul, hy]
      rw [← hx k, sub_self]
    have h := hαβ _ h0
    rw [map_sub, sub_eq_zero, map_sum] at h
    simp_rw [map_zsmul] at h
    exact h
  set d : Fin (Module.finrank ℤ L) → R := fun j => ∑ k, c k * (n k j : R) with hd
  have key : ∀ {X : Type} [AddCommGroup X] [Module R X] (φ : κ → X)
      (ψ : Fin (Module.finrank ℤ L) → X),
      (∀ k, φ k = ∑ j, n k j • ψ j) → ∑ k, c k • φ k = ∑ j, d j • ψ j := by
    intro X _ _ φ ψ h
    calc ∑ k, c k • φ k = ∑ k, ∑ j, (c k * (n k j : R)) • ψ j := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [h k, Finset.smul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Int.cast_smul_eq_zsmul R (n k j) (ψ j), smul_smul]
      _ = ∑ j, ∑ k, (c k * (n k j : R)) • ψ j := Finset.sum_comm
      _ = ∑ j, d j • ψ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hd, Finset.sum_smul]
  have hd0 : ∀ j, d j = 0 := by
    have h0 : ∑ j, d j • γ (b j : T) = 0 := by
      rw [← key (fun k => γ (α (x k))) (fun j => γ (b j : T)) (fun k => by
        show γ (α (x k)) = ∑ j, n k j • γ (b j : T)
        rw [hx k, map_sum]; simp_rw [map_zsmul])]
      exact hf
    exact Fintype.linearIndependent_iff.1 hγb d h0
  rw [key (fun k => β (x k)) (fun j => β (y j)) hβ]
  simp [hd0]

theorem aeval_eq_sum_coeff_smul {I F C : Type} [CommRing F] [CommRing C] [Algebra F C]
    (e : MvPolynomial I F →ₐ[F] C) (f : MvPolynomial I F) :
    e f = ∑ m ∈ f.support,
      MvPolynomial.coeff m f • e (MvPolynomial.map (Int.castRingHom F) (MvPolynomial.monomial m 1)) := by
  conv_lhs => rw [f.as_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, map_one, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul,
    mul_one]

theorem mvPolynomial_int_ringHom_ext {σ R : Type} [Semiring R]
    {f g : MvPolynomial σ ℤ →+* R} (hX : ∀ i, f (MvPolynomial.X i) = g (MvPolynomial.X i)) :
    f = g :=
  MvPolynomial.ringHom_ext
    (fun r => RingHom.congr_fun (RingHom.ext_int (f.comp MvPolynomial.C) (g.comp MvPolynomial.C)) r)
    hX

p2m_open "ModularCurve~baseChangeHom"

section Engine

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

local notation "Tp" => TateModule p J
local notation "EndT" => Module.End ℤ_[p] (TateModule p J)
local notation "EndV" => Module.End ℚ_[p] (RationalTateModule p J)
local notation "Ann" => Module.annihilator HeckeAlg J
local notation "𝒜" => Algebra.adjoin ℤ_[p] (Set.range (tateHeckeRep p J))

scoped instance isMulCommutative_intAlg : IsMulCommutative 𝒜 :=
  Algebra.isMulCommutative_adjoin ℤ_[p] (by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm])

open scoped IsMulCommutative in
scoped instance instCommRingIntAlg : CommRing 𝒜 := inferInstance

theorem tateHeckeRep_eq_zero_of_mem {t : HeckeAlg} (ht : t ∈ Ann) : tateHeckeRep p J t = 0 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun n => ?_)
  rw [coe_tateHeckeRep_apply_apply, LinearMap.zero_apply, TateModule.coe_zero, Pi.zero_apply]
  exact Module.mem_annihilator.1 ht _

def gamT : (HeckeAlg ⧸ Ann) →+* EndT :=
  Ideal.Quotient.lift Ann (tateHeckeRep p J) (fun _ ht => tateHeckeRep_eq_zero_of_mem p J ht)

theorem gamT_mk (t : HeckeAlg) : gamT p J (Ideal.Quotient.mk Ann t) = tateHeckeRep p J t :=
  Ideal.Quotient.lift_mk _ _ _

theorem tate_smul_eq_zero {a : ℤ_[p]} {x : Tp} (h : a • x = 0) (ha : a ≠ 0) : x = 0 := by
  have hspec := PadicInt.unitCoeff_spec ha
  set m := a.valuation
  have hpm : ((p : ℤ_[p]) ^ m) • x = 0 := by
    have : (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * a = (p : ℤ_[p]) ^ m := by
      calc (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * a
          = (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
              ((PadicInt.unitCoeff ha : ℤ_[p]) * (p : ℤ_[p]) ^ m) := congrArg _ hspec
        _ = (p : ℤ_[p]) ^ m := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [← this, mul_smul, h, smul_zero]
  refine Subtype.ext (funext fun n => ?_)
  have h1 := TateModule.compat_pow x n m
  have h2 : (((((p ^ m : ℕ) : ℤ_[p])) • x : Tp) : ℕ → J) (n + m) = 0 := by
    rw [Nat.cast_pow, hpm]; rfl
  rw [TateModule.natCast_padicInt_smul_apply] at h2
  rw [← h1, h2]
  rfl

scoped instance instNoZeroSMulDivisors : NoZeroSMulDivisors ℤ_[p] Tp :=
  ⟨fun {a x} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (tate_smul_eq_zero p J h ha)⟩

scoped instance instIsTorsionFreeT : Module.IsTorsionFree ℤ_[p] Tp := inferInstance

def toV : Tp →ₗ[ℤ_[p]] RationalTateModule p J := TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p J) 1

theorem toV_injective : Function.Injective (toV p J) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  haveI : IsLocalizedModule (nonZeroDivisors ℤ_[p])
      (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p J) 1) := inferInstance
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[p])
    (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p J) 1)).mp hx
  exact tate_smul_eq_zero p J hs (nonZeroDivisors.ne_zero s.2)

def jHom : EndT →ₐ[ℤ_[p]] EndV := Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)

theorem jHom_toV (f : EndT) (x : Tp) : jHom p J f (toV p J x) = toV p J (f x) := rfl

theorem jHom_injective : Function.Injective (jHom p J) := by
  intro f g hfg
  apply LinearMap.ext
  intro x
  apply toV_injective p J
  rw [← jHom_toV, ← jHom_toV, hfg]

theorem rationalHeckeRep_eq (t : HeckeAlg) :
    rationalHeckeRep p J t = jHom p J (tateHeckeRep p J t) := rfl

theorem jHom_algebraMap (z : ℤ_[p]) :
    jHom p J (algebraMap ℤ_[p] EndT z) = algebraMap ℚ_[p] EndV (z : ℚ_[p]) := by
  rw [(jHom p J).commutes]
  exact (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] EndV z)

theorem linearIndependent_of_jHom {ι : Type} (w : ι → EndT)
    (h : LinearIndependent ℚ_[p] (fun i => jHom p J (w i))) : LinearIndependent ℤ_[p] w := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s g hg i hi
  have h1 : ∑ i ∈ s, ((g i : ℤ_[p]) : ℚ_[p]) • jHom p J (w i) = 0 := by
    have h0 := congrArg (jHom p J) hg
    rw [map_sum, map_zero] at h0
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h0
    rw [map_smul, Algebra.smul_def, Algebra.smul_def, ← jHom_algebraMap, (jHom p J).commutes]
  have h2 : ((g i : ℤ_[p]) : ℚ_[p]) = 0 := h s (fun i => (g i : ℚ_[p])) h1 i hi
  exact PadicInt.coe_eq_zero.1 h2

variable [Module.Finite ℤ_[p] (TateModule p J)]

scoped instance instFiniteEndT : Module.Finite ℤ_[p] EndT := inferInstance

scoped instance instFiniteIntAlg : Module.Finite ℤ_[p] 𝒜 :=
  Module.Finite.of_injective (Subalgebra.val 𝒜).toLinearMap Subtype.val_injective

theorem engine {I : Type} (v : I → Nat.Primes) (O : Type) [CommRing O] (a : I → O)
    (hrel : ∀ f : MvPolynomial I ℤ,
      MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen (v i)) f ∈ Ann →
        MvPolynomial.eval₂Hom (Int.castRingHom O) a f = 0)
    (htf : ∀ (n : ℤ) (t : HeckeAlg), n ≠ 0 → (n : HeckeAlg) * t ∈ Ann → t ∈ Ann)
    (hfaith : ∀ {ι : Type} (t : ι → HeckeAlg),
      LinearIndependent ℤ (fun i => Ideal.Quotient.mk Ann (t i)) →
        LinearIndependent ℚ_[p] (fun i => rationalHeckeRep p J (t i)))
    (K : Type) [Field K] [IsAlgClosed K] (ιp : ℤ_[p] →+* K) (ιO : O →+* K) :
    ∃ Λ : 𝒜 →+* K, ∀ i : I, Λ ⟨tateHeckeRep p J (heckeGen (v i)),
        Algebra.subset_adjoin (Set.mem_range_self _)⟩ = ιO (a i) := by
  classical
  letI : Algebra ℤ_[p] K := ιp.toAlgebra

  let rJ : MvPolynomial I ℤ →+* HeckeAlg :=
    MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen (v i))
  let rO : MvPolynomial I ℤ →+* O := MvPolynomial.eval₂Hom (Int.castRingHom O) a
  let TV : I → 𝒜 := fun i =>
    ⟨tateHeckeRep p J (heckeGen (v i)), Algebra.subset_adjoin (Set.mem_range_self _)⟩
  let eV : MvPolynomial I ℤ_[p] →ₐ[ℤ_[p]] 𝒜 := MvPolynomial.aeval TV
  let eχ : MvPolynomial I ℤ_[p] →ₐ[ℤ_[p]] K := MvPolynomial.aeval (fun i => ιO (a i))
  have hrJ_X : ∀ i, rJ (MvPolynomial.X i) = heckeGen (v i) := fun i => MvPolynomial.eval₂_X _ _ _
  have hrO_X : ∀ i, rO (MvPolynomial.X i) = a i := fun i => MvPolynomial.eval₂_X _ _ _
  have heV_X : ∀ i, eV (MvPolynomial.X i) = TV i := fun i => MvPolynomial.aeval_X _ _
  have heχ_X : ∀ i, eχ (MvPolynomial.X i) = ιO (a i) := fun i => MvPolynomial.aeval_X _ _

  have hE1 : ∀ f : MvPolynomial I ℤ,
      ((eV (MvPolynomial.map (Int.castRingHom ℤ_[p]) f) : 𝒜) : EndT)
        = tateHeckeRep p J (rJ f) := by
    have key : ((Subalgebra.val 𝒜).toRingHom.comp
        (eV.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℤ_[p]))))
          = (tateHeckeRep p J).comp rJ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · rw [eq_intCast, map_intCast, map_intCast]
      · show ((eV (MvPolynomial.map (Int.castRingHom ℤ_[p]) (MvPolynomial.X i)) : 𝒜) : EndT)
          = tateHeckeRep p J (rJ (MvPolynomial.X i))
        rw [MvPolynomial.map_X, heV_X, hrJ_X]
    intro f
    exact RingHom.congr_fun key f

  have hE2 : ∀ f : MvPolynomial I ℤ,
      eχ (MvPolynomial.map (Int.castRingHom ℤ_[p]) f) = ιO (rO f) := by
    have key : (eχ.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℤ_[p])))
        = ιO.comp rO := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · rw [eq_intCast, map_intCast, map_intCast]
      · show eχ (MvPolynomial.map (Int.castRingHom ℤ_[p]) (MvPolynomial.X i))
          = ιO (rO (MvPolynomial.X i))
        rw [MvPolynomial.map_X, heχ_X, hrO_X]
    intro f
    exact RingHom.congr_fun key f

  have hker : ∀ f : MvPolynomial I ℤ_[p], eV f = 0 → eχ f = 0 := by
    intro f hf
    have hT := transfer_relation (R := ℤ_[p]) (T := HeckeAlg ⧸ Ann)
      (fun n w h => by
        by_cases hn : n = 0
        · exact Or.inl hn
        · right
          obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective w
          rw [zsmul_eq_mul, ← map_intCast (Ideal.Quotient.mk Ann), ← map_mul,
            Ideal.Quotient.eq_zero_iff_mem] at h
          exact Ideal.Quotient.eq_zero_iff_mem.2 (htf n t hn h))
      (((Ideal.Quotient.mk Ann).comp rJ).toAddMonoidHom) ((ιO.comp rO).toAddMonoidHom)
      (fun q hq => by
        have hq' : rJ q ∈ Ann := Ideal.Quotient.eq_zero_iff_mem.1 hq
        show ιO (rO q) = 0
        rw [hrel q hq', map_zero])
      (gamT p J).toAddMonoidHom
      (fun {ι} u hu => by
        choose t ht using fun i => Ideal.Quotient.mk_surjective (u i)
        have hu' : LinearIndependent ℤ (fun i => Ideal.Quotient.mk Ann (t i)) := by
          have : (fun i => Ideal.Quotient.mk Ann (t i)) = u := funext ht
          rw [this]; exact hu
        have h := hfaith t hu'
        have e : (fun i => (gamT p J).toAddMonoidHom (u i)) = fun i => tateHeckeRep p J (t i) := by
          funext i
          show gamT p J (u i) = tateHeckeRep p J (t i)
          rw [← ht i, gamT_mk]
        rw [e]
        exact linearIndependent_of_jHom p J _ h)
      (fun m : ↥f.support => (MvPolynomial.monomial (m : I →₀ ℕ) (1 : ℤ) : MvPolynomial I ℤ))
      (fun m => MvPolynomial.coeff (m : I →₀ ℕ) f)
      (by
        have h1 : ∀ m : ↥f.support,
            (gamT p J).toAddMonoidHom ((((Ideal.Quotient.mk Ann).comp rJ).toAddMonoidHom)
              (MvPolynomial.monomial (m : I →₀ ℕ) (1 : ℤ)))
              = ((eV (MvPolynomial.map (Int.castRingHom ℤ_[p])
                  (MvPolynomial.monomial (m : I →₀ ℕ) 1)) : 𝒜) : EndT) := fun m => by
          show gamT p J (Ideal.Quotient.mk Ann (rJ _)) = _
          rw [gamT_mk, hE1]
        simp_rw [h1]
        rw [Finset.sum_coe_sort f.support (fun m => MvPolynomial.coeff m f •
          ((eV (MvPolynomial.map (Int.castRingHom ℤ_[p]) (MvPolynomial.monomial m 1)) : 𝒜) :
            EndT))]
        have h2 : ((eV f : 𝒜) : EndT) = 0 := by rw [hf]; rfl
        rw [aeval_eq_sum_coeff_smul eV f, AddSubmonoidClass.coe_finsetSum] at h2
        simpa only [Subalgebra.coe_smul] using h2)

    rw [aeval_eq_sum_coeff_smul eχ f, ← Finset.sum_coe_sort]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hT
    rw [hE2]
    rfl

  letI : Algebra (MvPolynomial I ℤ_[p]) 𝒜 := eV.toRingHom.toAlgebra
  haveI : IsScalarTower ℤ_[p] (MvPolynomial I ℤ_[p]) 𝒜 :=
    IsScalarTower.of_algebraMap_eq (fun c => (eV.commutes c).symm)
  haveI : Algebra.IsIntegral ℤ_[p] 𝒜 := Algebra.IsIntegral.of_finite ℤ_[p] 𝒜
  haveI : Algebra.IsIntegral (MvPolynomial I ℤ_[p]) 𝒜 := Algebra.IsIntegral.tower_top (R := ℤ_[p])
  have hker' : RingHom.ker (algebraMap (MvPolynomial I ℤ_[p]) 𝒜) ≤ RingHom.ker eχ.toRingHom :=
    fun f hf => by
      rw [RingHom.mem_ker] at hf ⊢
      exact hker f hf
  obtain ⟨Λ, hΛ⟩ := RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed eχ.toRingHom hker'
  have hΛ' : ∀ f, Λ (eV f) = eχ f := fun f => RingHom.congr_fun hΛ f
  refine ⟨Λ, fun i => ?_⟩
  rw [← heχ_X i, ← hΛ', heV_X]

end Engine

section Concrete

variable (N : ℕ) [NeZero N] (hin : HeckeInputsAll N) (hcomm : HeckeOperatorsCommuteBar N)
include hin hcomm

theorem hrel_cusp (f : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N} ℤ)
    (hf : letI := heckeModuleBar N
      MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen i.1) f
        ∈ Module.annihilator HeckeAlg (JZero N)) :
    MvPolynomial.eval₂Hom (Int.castRingHom ↥(CuspForm.heckeAlgebra N 2 ∅))
      (fun i => CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2 (Set.notMem_empty _)) f = 0 := by
  letI := heckeModuleBar N
  obtain ⟨Φ, -, hΦ⟩ := exists_injective_ringHom_adjoin_heckeOperatorBar_cuspForm N hin hcomm

  obtain ⟨rJ, hrJ⟩ : ∃ rJ : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N} ℤ
      →+* HeckeAlg, rJ = MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen i.1) :=
    ⟨_, rfl⟩
  obtain ⟨rS, hrS⟩ : ∃ rS : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N} ℤ
      →+* ↥(CuspForm.heckeAlgebra N 2 ∅), rS = MvPolynomial.eval₂Hom
        (Int.castRingHom ↥(CuspForm.heckeAlgebra N 2 ∅))
        (fun i => CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2 (Set.notMem_empty _)) := ⟨_, rfl⟩
  rw [← hrJ] at hf
  rw [← hrS]
  have hrJ_X : ∀ i, rJ (MvPolynomial.X i) = heckeGen i.1 := fun i => by
    rw [hrJ]; exact MvPolynomial.eval₂_X _ _ _
  have hrS_X : ∀ i, rS (MvPolynomial.X i)
      = CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2 (Set.notMem_empty _) :=
    fun i => by rw [hrS]; exact MvPolynomial.eval₂_X _ _ _

  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N} ℤ →+*
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      ∀ q, ψ q = Φ (heckeEvalBarAux hcomm (rJ q)) :=
    ⟨Φ.comp ((heckeEvalBarAux hcomm).toRingHom.comp rJ), fun _ => rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N} ℤ →+*
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      ∀ q, θ q = ((rS q : ↥(CuspForm.heckeAlgebra N 2 ∅)) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
    ⟨(CuspForm.heckeAlgebra N 2 ∅).val.toRingHom.comp rS, fun _ => rfl⟩
  have hψX : ∀ i, ψ (MvPolynomial.X i) = CuspForm.heckeTLin 2 i.1.prop i.2 := fun i => by
    rw [hψ, hrJ_X i]
    exact (congrArg Φ (heckeEvalBarAux_heckeGen hcomm i.1)).trans (hΦ i.1 i.2)
  have hθX : ∀ i, θ (MvPolynomial.X i) = CuspForm.heckeTLin 2 i.1.prop i.2 := fun i => by
    rw [hθ, hrS_X i]
    rfl
  have key : ψ = θ := mvPolynomial_int_ringHom_ext fun i => (hψX i).trans (hθX i).symm
  have h1 : heckeEvalBar hcomm (rJ f) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [← heckeModuleBar_smul_def hcomm, LinearMap.zero_apply]
    exact Module.mem_annihilator.1 hf x
  have h2 : heckeEvalBarAux hcomm (rJ f) = 0 :=
    Subtype.ext ((heckeEvalBar_apply hcomm (rJ f)).symm.trans
      (h1.trans (ZeroMemClass.coe_zero _).symm))
  have h3 : Φ (heckeEvalBarAux hcomm (rJ f)) = ((rS f : ↥(CuspForm.heckeAlgebra N 2 ∅)) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
    (hψ f).symm.trans ((RingHom.congr_fun key f).trans (hθ f))
  have h4 : ((rS f : ↥(CuspForm.heckeAlgebra N 2 ∅)) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) = 0 :=
    h3.symm.trans ((congrArg Φ h2).trans (map_zero Φ))
  exact Subtype.ext (h4.trans (ZeroMemClass.coe_zero _).symm)

omit [NeZero N] hin hcomm in

theorem eq_zero_of_zsmul_of_injective {A V : Type} [Ring A] [AddCommGroup V] [Module ℂ V]
    (Φ : A →+* Module.End ℂ V) (hΦ : Function.Injective Φ) (n : ℤ) (hn : n ≠ 0) (a : A)
    (h : n • a = 0) : a = 0 := by
  apply hΦ
  rw [map_zero]
  have e1 : n • Φ a = 0 := by rw [← map_zsmul Φ, h, map_zero]
  refine LinearMap.ext fun x => ?_
  have e2 := LinearMap.congr_fun e1 x
  rw [LinearMap.smul_apply, LinearMap.zero_apply, ← Int.cast_smul_eq_zsmul ℂ] at e2
  rw [LinearMap.zero_apply]
  exact (smul_eq_zero.1 e2).resolve_left (Int.cast_ne_zero.2 hn)

theorem mem_annihilator_of_intCast_mul_mem (n : ℤ) (t : HeckeAlg) (hn : n ≠ 0)
    (h : letI := heckeModuleBar N
      (n : HeckeAlg) * t ∈ Module.annihilator HeckeAlg (JZero N)) :
    letI := heckeModuleBar N
    t ∈ Module.annihilator HeckeAlg (JZero N) := by
  letI := heckeModuleBar N
  obtain ⟨Φ, hΦinj, -⟩ := exists_injective_ringHom_adjoin_heckeOperatorBar_cuspForm N hin hcomm
  have h1 : heckeEvalBar hcomm ((n : HeckeAlg) * t) = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [← heckeModuleBar_smul_def hcomm, LinearMap.zero_apply]
    exact Module.mem_annihilator.1 h x
  have h2 : heckeEvalBarAux hcomm ((n : HeckeAlg) * t) = 0 :=
    Subtype.ext ((heckeEvalBar_apply hcomm _).symm.trans (h1.trans (ZeroMemClass.coe_zero _).symm))
  have e0 : n • heckeEvalBarAux hcomm t = 0 := by
    rw [← map_zsmul (heckeEvalBarAux hcomm) n t, zsmul_eq_mul]; exact h2
  have h4 : heckeEvalBarAux hcomm t = 0 := eq_zero_of_zsmul_of_injective Φ hΦinj n hn _ e0
  refine Module.mem_annihilator.2 fun x => ?_
  rw [heckeModuleBar_smul_def hcomm, heckeEvalBar_apply, h4, ZeroMemClass.coe_zero,
    LinearMap.zero_apply]

theorem hrel_intClosure {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hg : g.IsNormalizedEigenform) (hint : g.PrimeCoeffsIntegral)
    (f : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N} ℤ)
    (hf : letI := heckeModuleBar N
      MvPolynomial.eval₂Hom (Int.castRingHom HeckeAlg) (fun i => heckeGen i.1) f
        ∈ Module.annihilator HeckeAlg (JZero N)) :
    MvPolynomial.eval₂Hom (Int.castRingHom ↥(integralClosure ℤ ℂ))
      (fun i => CuspForm.eigenLift hint i.1) f = 0 := by
  have h0 := hrel_cusp N hin hcomm f hf
  obtain ⟨χ, -, hχT, -⟩ := hg.exists_ringHom_heckeAlgebra (∅ : Set ℕ)

  obtain ⟨rS, hrS⟩ : ∃ rS : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N} ℤ
      →+* ↥(CuspForm.heckeAlgebra N 2 ∅), rS = MvPolynomial.eval₂Hom
        (Int.castRingHom ↥(CuspForm.heckeAlgebra N 2 ∅))
        (fun i => CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2 (Set.notMem_empty _)) := ⟨_, rfl⟩
  obtain ⟨rO, hrO⟩ : ∃ rO : MvPolynomial {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N} ℤ
      →+* ↥(integralClosure ℤ ℂ), rO = MvPolynomial.eval₂Hom
        (Int.castRingHom ↥(integralClosure ℤ ℂ)) (fun i => CuspForm.eigenLift hint i.1) :=
    ⟨_, rfl⟩
  rw [← hrS] at h0
  rw [← hrO]
  have hrS_X : ∀ i, rS (MvPolynomial.X i)
      = CuspForm.heckeAlgebra.T (k := 2) i.1.prop i.2 (Set.notMem_empty _) :=
    fun i => by rw [hrS]; exact MvPolynomial.eval₂_X _ _ _
  have hrO_X : ∀ i, rO (MvPolynomial.X i) = CuspForm.eigenLift hint i.1 :=
    fun i => by rw [hrO]; exact MvPolynomial.eval₂_X _ _ _
  have key : (algebraMap ↥(integralClosure ℤ ℂ) ℂ).comp rO = χ.comp rS :=
    mvPolynomial_int_ringHom_ext fun i => by
      show algebraMap ↥(integralClosure ℤ ℂ) ℂ (rO (MvPolynomial.X i)) = χ (rS (MvPolynomial.X i))
      rw [hrO_X, hrS_X, hχT i.1 i.1.prop i.2 (Set.notMem_empty _)]
      exact CuspForm.eigenLift_coe hint i.1
  have h1 : algebraMap ↥(integralClosure ℤ ℂ) ℂ (rO f) = 0 := by
    rw [← RingHom.comp_apply, key, RingHom.comp_apply, h0, map_zero]
  exact Subtype.val_injective (h1.trans (ZeroMemClass.coe_zero _).symm)

end Concrete

namespace AlgClosedSub

variable {k : Type} [Field k] (φ : integralClosure ℤ ℂ →+* k)

local notation "ℤbar" => (integralClosure ℤ ℂ)

theorem ker_isMaximal (p : ℕ) [Fact p.Prime] [CharP k p] : (RingHom.ker φ).IsMaximal := by
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ) _ ?_
  have hp : (p : ℤ) ∈ (RingHom.ker φ).comap (algebraMap ℤ ℤbar) := by
    rw [Ideal.mem_comap, RingHom.mem_ker, map_natCast, map_natCast, CharP.cast_eq_zero]
  haveI : ((RingHom.ker φ).comap (algebraMap ℤ ℤbar)).IsPrime := Ideal.comap_isPrime _ _
  refine Ring.DimensionLEOne.maximalOfPrime (fun h => ?_) ‹_›
  rw [h, Ideal.mem_bot] at hp
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

abbrev F : Type := ℤbar ⧸ RingHom.ker φ

variable [(RingHom.ker φ).IsMaximal]

scoped instance instFieldF : Field (F φ) := Ideal.Quotient.field _

scoped instance isAlgClosed_F : IsAlgClosed (F φ) := by
  refine IsAlgClosed.of_exists_root _ (fun q hqm hirr => ?_)
  have hlift : q ∈ Polynomial.lifts (Ideal.Quotient.mk (RingHom.ker φ)) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr (fun n => Ideal.Quotient.mk_surjective _)
  obtain ⟨Q, hQ, hdeg, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hqm
  have hdeg' : (Q.map (algebraMap ℤbar ℂ)).degree ≠ 0 := by
    rw [hQm.degree_map, hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg'
  have hzint : IsIntegral ℤbar z := ⟨Q, hQm, by rwa [← Polynomial.eval_map]⟩
  have hzZ : IsIntegral ℤ z := isIntegral_trans z hzint
  refine ⟨Ideal.Quotient.mk _ ⟨z, hzZ⟩, ?_⟩
  have hQz : Q.eval (⟨z, hzZ⟩ : ℤbar) = 0 := by
    apply Subtype.val_injective
    have h := Polynomial.eval₂_at_apply (algebraMap ℤbar ℂ) (⟨z, hzZ⟩ : ℤbar) (p := Q)
    rw [← Polynomial.eval_map] at h
    change (algebraMap ℤbar ℂ) (Q.eval ⟨z, hzZ⟩) = 0
    rw [← h]
    exact hz
  rw [← hQ, Polynomial.eval_map, Polynomial.eval₂_at_apply, hQz, map_zero]

def phiBar : F φ →+* k := Ideal.Quotient.lift _ φ (fun _ h => h)

omit [(RingHom.ker φ).IsMaximal] in
theorem phiBar_mk (a : ℤbar) : phiBar φ (Ideal.Quotient.mk _ a) = φ a :=
  Ideal.Quotient.lift_mk _ _ _

theorem charP_F (p : ℕ) [CharP k p] : CharP (F φ) p :=
  (RingHom.charP_iff_charP (phiBar φ) p).2 ‹_›

def padicIntToF (p : ℕ) [Fact p.Prime] [CharP k p] : ℤ_[p] →+* F φ :=
  haveI := charP_F φ p
  (ZMod.castHom (dvd_refl p) (F φ)).comp PadicInt.toZMod

end AlgClosedSub

open AlgClosedSub in

theorem main (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : HeckeInputsAll N) (hcomm : HeckeOperatorsCommuteBar N)
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform)
    {k : Type} [Field k] [CharP k p] (φ : integralClosure ℤ ℂ →+* k) :
    letI := heckeModuleBar N
    ∃ ψ : ↥(Algebra.adjoin ℤ_[p] (Set.range (tateHeckeRep p (JZero N)))) →+* k,
      ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
          ψ ⟨tateHeckeRep p (JZero N) (heckeGen ℓ), Algebra.subset_adjoin (Set.mem_range_self _)⟩
            = φ a := by
  letI := heckeModuleBar N
  haveI : Module.Finite ℤ_[p] (TateModule p (JZero N)) := moduleFinite_padicInt_tateModule_jZero N p
  haveI := AlgClosedSub.ker_isMaximal φ p
  have hint : g.PrimeCoeffsIntegral := hg.primeCoeffsIntegral_of_neZero

  have E1 := engine p (JZero N) (I := {ℓ : Nat.Primes // ¬ (ℓ : ℕ) ∣ N}) (fun i => i.1)
    ↥(integralClosure ℤ ℂ) (fun i => CuspForm.eigenLift hint i.1)
  have E2 := E1 (fun f hf => hrel_intClosure N hin hcomm hg hint f hf)
  have E3 := E2 (fun n t hn h => mem_annihilator_of_intCast_mul_mem N hin hcomm n t hn h)
  have E4 := E3 (fun t ht => linearIndependent_rationalHeckeRep_of_linearIndependent N p hin hcomm t ht)
  have E5 := E4 (AlgClosedSub.F φ) (AlgClosedSub.padicIntToF φ p)
    (Ideal.Quotient.mk (RingHom.ker φ))
  cases E5 with
  | intro Λ hΛ =>
    refine ⟨(AlgClosedSub.phiBar φ).comp Λ, fun ℓ hℓN => ⟨CuspForm.eigenLift hint ℓ,
      CuspForm.eigenLift_coe hint ℓ, ?_⟩⟩
    have h1 := hΛ ⟨ℓ, hℓN⟩
    rw [RingHom.comp_apply, h1]
    exact AlgClosedSub.phiBar_mk φ _

end W7HA1

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform)
    {k : Type} [Field k] [CharP k p] (φ : integralClosure ℤ ℂ →+* k) :
    letI := ModularCurve.heckeModuleBar N
    ∃ ψ : ↥(Algebra.adjoin ℤ_[p]
        (Set.range (ModularCurve.tateHeckeRep p (ModularCurve.JZero N)))) →+* k,
      ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ N →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
          ψ ⟨ModularCurve.tateHeckeRep p (ModularCurve.JZero N) (ModularCurve.heckeGen ℓ),
              Algebra.subset_adjoin (Set.mem_range_self _)⟩ = φ a :=
  W7HA1.main N p hin hcomm hg φ

end
end S_CuspForm_IsNormalizedEigenform_exists_ringHom_adjoin_tateHeckeRep_jZero_eq_residual
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_ringHom_adjoin_tateHeckeRep_jZero_eq_residual (solution)

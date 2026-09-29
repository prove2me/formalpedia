-- Prove2me | solution 1 for CuspForm.IsNewform.heckeU_eq_intCast_smul_of_mem_heckeEigenspace_tateModule_jZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5d83fc82-b434-5952-9678-c349d2939831

import Mathlib
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CuspForm_exists_qCoeff_conj
import Theorems.Thm_Module_End_finrank_iInf_eigenspace_baseChange_eq
import Theorems.Thm_Module_End_finrank_iInf_eigenspace_baseChange_complex_eq_add
import Theorems.Thm_CuspForm_IsNewform_finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one
import Theorems.Thm_CuspForm_heckeTLin_comm
import Theorems.Thm_CuspForm_heckeTLin_heckeULin_comm
import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_sq_eq_one_of_isNewform
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_heckeU_eq_intCast_smul_of_mem_heckeEigenspace_tateModule_jZero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open scoped TensorProduct

namespace HeckeUEigenspaceTate

section Bridge

variable {p : ℕ} [Fact p.Prime] {J : Type} [AddCommGroup J] [Module ModularCurve.HeckeAlg J]

theorem mem_root_of_mem {x : ℕ → J} (hx : x ∈ ModularCurve.TateModule p J) :
    x ∈ _root_.TateModule p J := by
  change ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n
  intro n
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_smul_eq_nsmul ℤ]; exact ModularCurve.TateModule.pow_smul_apply hx n
  · rw [Nat.cast_smul_eq_nsmul ℤ]; exact hx.2 n

theorem mem_of_mem_root {x : ℕ → J} (hx : x ∈ _root_.TateModule p J) :
    x ∈ ModularCurve.TateModule p J := by
  change ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n at hx
  refine ⟨?_, fun n => ?_⟩
  · have h := (hx 0).1
    rwa [pow_zero, Nat.cast_one, one_smul] at h
  · have h := (hx n).2
    rwa [Nat.cast_smul_eq_nsmul ℤ] at h

theorem toZModPow_val (n : ℕ) (a : ℤ_[p]) : (PadicInt.toZModPow n a).val = a.appr n := by
  show (((a.appr n : ℕ) : ZMod (p ^ n))).val = a.appr n
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt a n)]

variable [Module ℤ_[p] (ModularCurve.TateModule p J)]
variable (hsmul : ∀ (a : ℤ_[p]) (x : ModularCurve.TateModule p J) (n : ℕ),
  ((a • x : ModularCurve.TateModule p J) : ℕ → J) n =
    (PadicInt.toZModPow n a).val • (x : ℕ → J) n)

def β : ModularCurve.TateModule p J ≃ₗ[ℤ_[p]] _root_.TateModule p J where
  toFun x := ⟨x, mem_root_of_mem x.2⟩
  invFun y := ⟨y, mem_of_mem_root y.2⟩
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    funext n
    show ((a • x : ModularCurve.TateModule p J) : ℕ → J) n =
      ((a.appr n : ℕ) : ℤ) • (x : ℕ → J) n
    rw [hsmul, toZModPow_val, Nat.cast_smul_eq_nsmul ℤ]
  left_inv _ := rfl
  right_inv _ := rfl

theorem β_hecke (t : ModularCurve.HeckeAlg) (x : ModularCurve.TateModule p J) :
    β hsmul (t • x) = ModularCurve.tateHeckeRep p J t (β hsmul x) :=
  Subtype.ext rfl

end Bridge

section Transport

theorem cancel_conj (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    {N : Type*} [AddCommGroup N] [Module R N] (f : Module.End R N) :
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B N).toLinearMap ∘ₗ
        (f.baseChange A).baseChange B =
      f.baseChange B ∘ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B N).toLinearMap := by
  rw [LinearMap.baseChange_baseChange]
  ext x
  simp

theorem cancel_nat (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    {N : Type*} [AddCommGroup N] [Module R N] (f : Module.End R N) (m : B) (y : A ⊗[R] N) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B N (m ⊗ₜ f.baseChange A y) =
      f.baseChange B (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B N (m ⊗ₜ y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | tmul a n =>
    rw [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.baseChange_tmul]
  | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]

theorem iInf_eigenspace_conj {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V]
    [AddCommGroup V'] [Module R V] [Module R V'] (e : V ≃ₗ[R] V') {ι : Type*}
    (f : ι → Module.End R V) (f' : ι → Module.End R V')
    (h : ∀ i, e.toLinearMap ∘ₗ f i = f' i ∘ₗ e.toLinearMap) (μ : ι → R) :
    (⨅ i, Module.End.eigenspace (f' i) (μ i)) =
      (⨅ i, Module.End.eigenspace (f i) (μ i)).map e.toLinearMap := by
  rw [← LinearEquiv.symm_symm e, ← Submodule.comap_equiv_eq_map_symm]
  ext x
  simp only [Submodule.mem_comap, Submodule.mem_iInf, Module.End.mem_eigenspace_iff,
    LinearEquiv.coe_coe]
  refine forall_congr' fun i => ?_
  have hi : ∀ y, e (f i y) = f' i (e y) := fun y => congrArg (fun g => g y) (h i)
  constructor
  · intro hx
    apply e.injective
    rw [hi, LinearEquiv.apply_symm_apply, hx, map_smul, LinearEquiv.apply_symm_apply]
  · intro hx
    have := hi (e.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, hx, map_smul, LinearEquiv.apply_symm_apply]

theorem finrank_iInf_eigenspace_conj {R : Type*} [Field R] {V V' : Type*} [AddCommGroup V]
    [AddCommGroup V'] [Module R V] [Module R V'] (e : V ≃ₗ[R] V') {ι : Type*}
    (f : ι → Module.End R V) (f' : ι → Module.End R V')
    (h : ∀ i, e.toLinearMap ∘ₗ f i = f' i ∘ₗ e.toLinearMap) (μ : ι → R) :
    Module.finrank R ↥(⨅ i, Module.End.eigenspace (f' i) (μ i)) =
      Module.finrank R ↥(⨅ i, Module.End.eigenspace (f i) (μ i)) := by
  rw [iInf_eigenspace_conj e f f' h μ, LinearEquiv.finrank_map_eq]

end Transport

section Algebra

theorem injective_of_isIntegral_of_charZero {R₀ K : Type*} [CommRing R₀] [IsDomain R₀]
    [Algebra.IsIntegral ℤ R₀] [Field K] [CharZero K] (φ : R₀ →+* K) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [show Ideal.comap (algebraMap ℤ R₀) (RingHom.ker φ) = RingHom.ker (φ.comp (algebraMap ℤ R₀))
    from RingHom.comap_ker φ (algebraMap ℤ R₀)]
  have : φ.comp (algebraMap ℤ R₀) = Int.castRingHom K := RingHom.ext_int _ _
  rw [this, ← RingHom.injective_iff_ker_eq_bot]
  exact Int.cast_injective

open ModularFormClass in
theorem isNormalizedEigenform_of_qCoeff_eq_conj {N : ℕ}
    {f f' : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (h : ∀ n, qCoeff f' n = starRingEnd ℂ (qCoeff f n)) : f'.IsNormalizedEigenform where
  qCoeff_one := by rw [h, hf.qCoeff_one, map_one]
  qCoeff_mul_of_coprime m n hmn := by rw [h, h, h, hf.qCoeff_mul_of_coprime m n hmn, map_mul]
  qCoeff_prime_pow_of_not_dvd q r hq hqN := by
    rw [h, h, h, h, hf.qCoeff_prime_pow_of_not_dvd q r hq hqN, map_sub, map_mul, map_mul,
      map_natCast]
  qCoeff_prime_pow_of_dvd q r hq hqN := by
    rw [h, h, h, hf.qCoeff_prime_pow_of_dvd q r hq hqN, map_mul]

open ModularFormClass in

theorem isNewform_of_qCoeff_eq_conj {N : ℕ} [NeZero N]
    {g g' : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNewform)
    (h : ∀ n, qCoeff g' n = starRingEnd ℂ (qCoeff g n)) : g'.IsNewform := by
  refine ⟨isNormalizedEigenform_of_qCoeff_eq_conj hg.1 h, fun M hM hMN hocc => ?_⟩
  haveI : NeZero M := ⟨fun h0 => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h0 ▸ hM))⟩
  obtain ⟨g₀, hg₀, hg₀q⟩ := hocc
  obtain ⟨ρ, hρ⟩ := CuspForm.exists_qCoeff_conj M 2
  refine hg.2 M hM hMN ⟨ρ g₀, isNormalizedEigenform_of_qCoeff_eq_conj hg₀ (hρ g₀), ?_⟩
  intro ℓ hℓ hℓN
  rw [hρ, hg₀q ℓ hℓ hℓN, h, Complex.conj_conj]

open ModularFormClass in

theorem exists_int_qCoeff_eq {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNewform) (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) :
    ∃ a : ℤ, (a = 0 ∨ a = 1 ∨ a = -1) ∧ qCoeff g q = (a : ℂ) := by
  by_cases hsq : q ^ 2 ∣ M
  · exact ⟨0, Or.inl rfl, by rw [CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hg q hq hsq, Int.cast_zero]⟩
  · have h1 := CuspForm.qCoeff_sq_eq_one_of_isNewform hg q hq hqM hsq
    rcases sq_eq_one_iff.mp h1 with h | h
    · exact ⟨1, Or.inr (Or.inl rfl), by rw [h, Int.cast_one]⟩
    · exact ⟨-1, Or.inr (Or.inr rfl), by rw [h, Int.cast_neg, Int.cast_one]⟩

end Algebra

section Forms

open ModularFormClass

variable {M : ℕ} [NeZero M] (S : Finset ℕ)

abbrev I (M : ℕ) (S : Finset ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S}

private def _root_.HeckeUEigenspaceTate.T (ℓ : I M S) : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1

p2m_export "HeckeUEigenspaceTate" "T"
theorem T_comm (ℓ ℓ' : I M S) : Commute (T S ℓ) (T S ℓ') :=
  CuspForm.heckeTLin_comm 2 ℓ.2.1 ℓ.2.2.1 ℓ'.2.1 ℓ'.2.2.1

def Esp (μ : I M S → ℂ) : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  ⨅ ℓ, Module.End.eigenspace (T S ℓ) (μ ℓ)

theorem mem_Esp {μ : I M S → ℂ} {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} :
    f ∈ Esp S μ ↔ ∀ ℓ, T S ℓ f = μ ℓ • f := by
  simp [Esp, Submodule.mem_iInf]

theorem iSupIndep_Esp : iSupIndep (fun μ : I M S → ℂ => Esp S μ) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (T (M := M) S)
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (T_comm S j i) φ)
  refine h.mono fun μ => ?_
  exact iInf_mono fun ℓ => Module.End.eigenspace_le_maxGenEigenspace

theorem U_mem_Esp {q : ℕ} (hqM : q ∣ M) {μ : I M S → ℂ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f ∈ Esp S μ) :
    CuspForm.heckeULin 2 hqM f ∈ Esp S μ := by
  rw [mem_Esp] at hf ⊢
  intro ℓ
  have hc := CuspForm.heckeTLin_heckeULin_comm (N := M) 2 ℓ.2.1 ℓ.2.2.1 hqM
  show CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1 (CuspForm.heckeULin 2 hqM f) = _
  rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
  show CuspForm.heckeULin 2 hqM (T S ℓ f) = _
  rw [hf ℓ, map_smul]

def 𝓑 : Set (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  {F | ∃ (R d : ℕ) (hdRM : d * R ∣ M) (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
    CuspForm.IsNewform g' ∧ F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g'}

theorem span_𝓑 : Submodule.span ℂ (𝓑 (M := M)) = ⊤ :=
  CuspForm.span_rescaleLin_isNewform_eq_top M

theorem neZero_of_mul_dvd {R d : ℕ} (hdRM : d * R ∣ M) : NeZero R :=
  ⟨by rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (by simpa using hdRM))⟩

theorem rescale_mem_Esp {R d : ℕ} (hdRM : d * R ∣ M)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg' : CuspForm.IsNewform g') :
    FreyPackage.ModMCarrier.rescaleLin hdRM 2 g' ∈ Esp S (fun ℓ => qCoeff g' ℓ) := by
  haveI : NeZero R := neZero_of_mul_dvd hdRM
  rw [mem_Esp]
  intro ℓ
  have hℓR : ¬ (ℓ : ℕ) ∣ R := fun h => ℓ.2.2.1 (h.trans ((Dvd.intro_left d rfl).trans hdRM))
  have heig := ((CuspForm.isNormalizedEigenform_iff_heckeTLin g').1 hg'.1).2 ℓ ℓ.2.1
  rw [T, CuspForm.heckeTLin_rescaleLin hdRM ℓ.2.1 ℓ.2.2.1 hℓR g', (heig.1 hℓR), map_smul]

theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  rw [ModularForm.val_heckeDiagMatrix one_ne_zero, Units.val_one, Matrix.one_fin_two]
  simp

theorem rescaleLin_one (h : 1 * M ∣ M) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    FreyPackage.ModMCarrier.rescaleLin h 2 f = f := by
  apply DFunLike.coe_injective
  show ⇑(FreyPackage.ModMCarrier.rescaleLin h 2 f) = ⇑f
  rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one]
  exact SlashAction.slash_one 2 ⇑f

variable {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)

def cg (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) : I M S → ℂ := fun ℓ => qCoeff g ℓ

include hg in
theorem g_mem_Esp : g ∈ Esp S (cg S g) := by
  rw [mem_Esp]
  intro ℓ
  exact (((CuspForm.isNormalizedEigenform_iff_heckeTLin g).1 hg.1).2 ℓ ℓ.2.1).1 ℓ.2.2.1

include hg in
theorem U_g {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm.heckeULin 2 hqM g = qCoeff g q • g :=
  (((CuspForm.isNormalizedEigenform_iff_heckeTLin g).1 hg.1).2 q hq).2 hqM

include hg in

theorem rescale_eq_of_packet_eq {R d : ℕ} (hdRM : d * R ∣ M)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg' : CuspForm.IsNewform g')
    (hpk : (fun ℓ : I M S => qCoeff g' ℓ) = cg S g) :
    FreyPackage.ModMCarrier.rescaleLin hdRM 2 g' = g := by

  let P : ℕ := ∏ q ∈ S, max q 1
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one (le_max_right q 1))
  haveI : NeZero (M * P) := ⟨mul_ne_zero (NeZero.ne M) hP⟩
  have hR : R ∣ M * P := ((Dvd.intro_left d rfl).trans hdRM).trans (Dvd.intro _ rfl)
  have hM : M ∣ M * P := Dvd.intro _ rfl
  have h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M * P → qCoeff g' ℓ = qCoeff g ℓ := by
    intro ℓ hℓ hℓMP
    have hℓM : ¬ ℓ ∣ M := fun h => hℓMP (h.mul_right P)
    have hℓS : ℓ ∉ S := by
      intro hS
      apply hℓMP
      have h1 : max ℓ 1 ∣ P := Finset.dvd_prod_of_mem (fun q => max q 1) hS
      rw [max_eq_left hℓ.one_lt.le] at h1
      exact h1.mul_left M
    exact congrFun hpk ⟨ℓ, hℓ, hℓM, hℓS⟩
  obtain ⟨hRM, hq⟩ := CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq hg' hg hR hM h
  subst hRM
  have hgg : g' = g :=
    CuspForm.IsNormalizedEigenform.eq_of_forall_prime_qCoeff_eq hg'.1 hg.1 fun p _ => hq p
  subst hgg

  have hd : d = 1 := by
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact NeZero.ne R (Nat.eq_zero_of_zero_dvd (by simpa using hdRM))
    have hle : d * R ≤ 1 * R := by
      rw [one_mul]; exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne R)) hdRM
    have : d ≤ 1 := Nat.le_of_mul_le_mul_right hle (Nat.pos_of_ne_zero (NeZero.ne R))
    omega
  subst hd
  exact rescaleLin_one hdRM g'

def W'' (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  ⨆ μ ∈ {μ : I M S → ℂ | μ ≠ cg S g}, Esp S μ

include hg in
theorem 𝓑_subset : 𝓑 (M := M) ⊆ ↑((ℂ ∙ g) ⊔ W'' S g) := by
  rintro F ⟨R, d, hdRM, g', hg', rfl⟩
  by_cases hpk : (fun ℓ : I M S => qCoeff g' ℓ) = cg S g
  · rw [rescale_eq_of_packet_eq S hg hdRM g' hg' hpk]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self g)
  · have hmem := rescale_mem_Esp S hdRM g' hg'
    exact Submodule.mem_sup_right
      ((le_biSup (fun μ => Esp S μ) hpk : Esp S (fun ℓ : I M S => qCoeff g' ℓ) ≤ W'' S g) hmem)

include hg in
theorem sup_eq_top : (ℂ ∙ g) ⊔ W'' S g = ⊤ := by
  rw [eq_top_iff, ← span_𝓑 (M := M), Submodule.span_le]
  exact 𝓑_subset S hg

theorem U_mem_W'' {q : ℕ} (hqM : q ∣ M) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hf : f ∈ W'' S g) : CuspForm.heckeULin 2 hqM f ∈ W'' S g := by
  have h : (W'' S g).map (CuspForm.heckeULin 2 hqM) ≤ W'' S g := by
    rw [W'', Submodule.map_iSup]
    refine iSup_mono fun μ => ?_
    rw [Submodule.map_iSup]
    refine iSup_mono fun hμ => ?_
    rintro _ ⟨f, hf, rfl⟩
    exact U_mem_Esp S hqM hf
  exact h ⟨f, hf, rfl⟩

def Edual (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    Submodule ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) :=
  ⨅ ℓ : I M S, Module.End.eigenspace (T S ℓ).dualMap (cg S g ℓ)

theorem mem_Edual {v : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)} :
    v ∈ Edual S g ↔ ∀ (ℓ : I M S) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2),
      v (T S ℓ f) = cg S g ℓ * v f := by
  simp only [Edual, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  refine forall_congr' fun ℓ => ?_
  rw [LinearMap.ext_iff]
  refine forall_congr' fun f => ?_
  rw [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul]

theorem apply_eq_zero_of_mem_Esp {v : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)}
    (hv : v ∈ Edual S g) {μ : I M S → ℂ} (hμ : μ ≠ cg S g)
    {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f ∈ Esp S μ) : v f = 0 := by
  obtain ⟨ℓ, hℓ⟩ := Function.ne_iff.mp hμ
  have h1 := (mem_Edual S).mp hv ℓ f
  have h2 := (mem_Esp S).mp hf ℓ
  rw [h2, map_smul, smul_eq_mul] at h1
  have h3 : (μ ℓ - cg S g ℓ) * v f = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hℓ)

theorem apply_eq_zero_of_mem_W'' {v : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)}
    (hv : v ∈ Edual S g) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f ∈ W'' S g) :
    v f = 0 := by
  have hle : W'' S g ≤ LinearMap.ker v := by
    rw [W'']
    refine iSup₂_le fun μ hμ => ?_
    intro f hf
    exact apply_eq_zero_of_mem_Esp S hv hμ hf
  exact hle hf

include hg in

theorem dualMap_U_eq_smul {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    {v : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)} (hv : v ∈ Edual S g) :
    (CuspForm.heckeULin 2 hqM).dualMap v = qCoeff g q • v := by
  refine LinearMap.ext_on (s := (((ℂ ∙ g) ⊔ W'' S g : Submodule ℂ _) : Set _))
    (by rw [Submodule.span_eq, sup_eq_top S hg]) ?_
  intro f hf
  rw [SetLike.mem_coe] at hf
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hx
  simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, map_add, map_smul,
    U_g hg hq hqM, apply_eq_zero_of_mem_W'' S hv hw,
    apply_eq_zero_of_mem_W'' S hv (U_mem_W'' S hqM hw), smul_eq_mul, add_zero, mul_zero]

include hg in

theorem Edual_le_eigenspace_U {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) :
    Edual S g ≤ Module.End.eigenspace (CuspForm.heckeULin (N := M) 2 hqM).dualMap (qCoeff g q) := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff]
  exact dualMap_U_eq_smul S hg hq hqM hv

end Forms

section Counts

open ModularFormClass

variable {S₂ : Type*} [AddCommGroup S₂] [Module ℂ S₂]

theorem real_smul_dual (r : ℝ) (v : Module.Dual ℂ S₂) : r • v = (r : ℂ) • v := by
  ext f
  simp [Complex.real_smul]

theorem hli_of_linearIndependent {n : ℕ} {Λ : Submodule ℤ (Module.Dual ℂ S₂)}
    (b : Module.Basis (Fin n) ℤ Λ)
    (hli : LinearIndependent ℝ (fun i => ((b i : Λ) : Module.Dual ℂ S₂))) :
    ∀ r : Fin n → ℝ, ∑ i, ((r i : ℂ)) • ((b i : Λ) : Module.Dual ℂ S₂) = 0 → r = 0 := by
  intro r hr
  have h := Fintype.linearIndependent_iff.mp hli r
  have : ∑ i, r i • ((b i : Λ) : Module.Dual ℂ S₂) = 0 := by
    rw [← hr]
    exact Finset.sum_congr rfl fun i _ => real_smul_dual _ _
  funext i
  exact h this i

theorem hsp_of_span_eq_top {n : ℕ} {Λ : Submodule ℤ (Module.Dual ℂ S₂)}
    (b : Module.Basis (Fin n) ℤ Λ)
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : Λ) : Module.Dual ℂ S₂)) = ⊤) :
    ∀ v : Module.Dual ℂ S₂, ∃ r : Fin n → ℝ,
      ∑ i, ((r i : ℂ)) • ((b i : Λ) : Module.Dual ℂ S₂) = v := by
  intro v
  have hv : v ∈ Submodule.span ℝ (Set.range fun i => ((b i : Λ) : Module.Dual ℂ S₂)) := by
    rw [hsp]; trivial
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  refine ⟨r, ?_⟩
  rw [← hr]
  exact Finset.sum_congr rfl fun i _ => (real_smul_dual _ _).symm

variable {M : ℕ} [NeZero M]

theorem isIntegral_range (S : Finset ℕ) (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ) :
    Algebra.IsIntegral ℤ chig.range := by
  haveI := CuspForm.moduleFinite_heckeAlgebra_two M (↑S : Set ℕ)
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := RingHom.rangeRestrict_surjective chig x
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) y).map chig.rangeRestrict.toIntAlgHom

theorem finrank_field_of_complex_counts (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    {ι : Type} (Aι : ι → Module.End ℤ (ModularCurve.periodLattice M))
    (Dι : ι → Module.End ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)))
    (hAD : ∀ (i : ι) (x : ModularCurve.periodLattice M),
      ((Aι i x : ModularCurve.periodLattice M) : Module.Dual ℂ _) = Dι i (x : Module.Dual ℂ _))
    (cR : ι → chig.range)
    (h1 : Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (Dι i) ((cR i : ℂ))) = 1)
    (h2 : Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (Dι i) (starRingEnd ℂ (cR i : ℂ))) = 1)
    (K : Type) [Field K] [CharZero K] (φ : chig.range →+* K) :
    Module.finrank K ↥(⨅ i, Module.End.eigenspace ((Aι i).baseChange K) (φ (cR i))) = 2 := by
  classical
  haveI : Algebra.IsIntegral ℤ chig.range := isIntegral_range S chig
  have hφ : Function.Injective φ := injective_of_isIntegral_of_charZero φ

  let Fr := FractionRing chig.range
  let σK : Fr →+* K := IsFractionRing.lift hφ
  let σC : Fr →+* ℂ := IsFractionRing.lift (g := chig.range.subtype) Subtype.val_injective
  let F : Subfield ℂ := σC.fieldRange
  have hσC : Function.Bijective σC.rangeRestrictField := by
    refine ⟨fun x y hxy => σC.injective ?_, fun y => ?_⟩
    · have := congrArg (fun z : F => (z : ℂ)) hxy
      simpa only [RingHom.coe_rangeRestrictField] using this
    · obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.mp y.2
      exact ⟨x, Subtype.ext (by rw [RingHom.coe_rangeRestrictField, hx])⟩
  let ιF : Fr ≃+* F := RingEquiv.ofBijective σC.rangeRestrictField hσC
  let τK : F →+* K := σK.comp ιF.symm.toRingHom
  letI : Algebra F K := τK.toAlgebra
  obtain ⟨n, b, hli, hsp⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top M
  haveI : Module.Finite F (F ⊗[ℤ] ModularCurve.periodLattice M) :=
    Module.Finite.of_basis (b.baseChange F)
  let TF : ι → Module.End F (F ⊗[ℤ] ModularCurve.periodLattice M) :=
    fun i => (Aι i).baseChange F
  let cF : ι → F := fun i => ιF (algebraMap chig.range Fr (cR i))
  have hK := Module.End.finrank_iInf_eigenspace_baseChange_eq F K TF cF
  have hC := Module.End.finrank_iInf_eigenspace_baseChange_eq F ℂ TF cF

  have hcK : ∀ i, algebraMap F K (cF i) = φ (cR i) := fun i => by
    show σK (ιF.symm (ιF (algebraMap _ Fr (cR i)))) = φ (cR i)
    rw [RingEquiv.symm_apply_apply]
    exact IsFractionRing.lift_algebraMap hφ (cR i)
  have hcC : ∀ i, algebraMap F ℂ (cF i) = (cR i : ℂ) := fun i => by
    show ((σC.rangeRestrictField (algebraMap _ Fr (cR i)) : F) : ℂ) = (cR i : ℂ)
    rw [RingHom.coe_rangeRestrictField, IsFractionRing.lift_algebraMap]
    rfl

  have hTK : Module.finrank K ↥(⨅ i, Module.End.eigenspace ((Aι i).baseChange K)
      (φ (cR i))) = Module.finrank K ↥(⨅ i,
        Module.End.eigenspace ((TF i).baseChange K) (algebraMap F K (cF i))) := by
    rw [show (⨅ i, Module.End.eigenspace ((Aι i).baseChange K) (φ (cR i))) =
        ⨅ i, Module.End.eigenspace ((Aι i).baseChange K) (algebraMap F K (cF i)) from
      iInf_congr fun i => by rw [hcK]]
    exact finrank_iInf_eigenspace_conj
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ F K K (ModularCurve.periodLattice M))
      (fun i => (TF i).baseChange K) (fun i => (Aι i).baseChange K)
      (fun i => cancel_conj ℤ F K (Aι i)) (fun i => algebraMap F K (cF i))
  have hTC : Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace ((Aι i).baseChange ℂ)
      ((cR i : ℂ))) = Module.finrank ℂ ↥(⨅ i,
        Module.End.eigenspace ((TF i).baseChange ℂ) (algebraMap F ℂ (cF i))) := by
    rw [show (⨅ i, Module.End.eigenspace ((Aι i).baseChange ℂ) ((cR i : ℂ))) =
        ⨅ i, Module.End.eigenspace ((Aι i).baseChange ℂ) (algebraMap F ℂ (cF i)) from
      iInf_congr fun i => by rw [hcC]]
    exact finrank_iInf_eigenspace_conj
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ F ℂ ℂ (ModularCurve.periodLattice M))
      (fun i => (TF i).baseChange ℂ) (fun i => (Aι i).baseChange ℂ)
      (fun i => cancel_conj ℤ F ℂ (Aι i)) (fun i => algebraMap F ℂ (cF i))

  have hcx : Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace ((Aι i).baseChange ℂ)
      ((cR i : ℂ))) = 2 := by
    rw [Module.End.finrank_iInf_eigenspace_baseChange_complex_eq_add (ModularCurve.periodLattice M)
      b (hli_of_linearIndependent b hli) (hsp_of_span_eq_top b hsp) Dι Aι hAD
      (fun i => (cR i : ℂ)), h1, h2]
  rw [hTK, hK, ← hC, ← hTC, hcx]

end Counts

section PeriodSide

open ModularFormClass

variable {M : ℕ} [NeZero M]

def A (S : Finset ℕ) (ℓ : I M S) : Module.End ℤ (ModularCurve.periodLattice M) :=
  ModularCurve.periodLatticeHeckeEnd M (ModularCurve.heckeGen ⟨ℓ.1, ℓ.2.1⟩)

def D (S : Finset ℕ) (ℓ : I M S) :
    Module.End ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) :=
  (CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1).dualMap

theorem coe_A_apply (S : Finset ℕ) (ℓ : I M S) (x : ModularCurve.periodLattice M) :
    ((A S ℓ x : ModularCurve.periodLattice M) : Module.Dual ℂ _) = D S ℓ (x : Module.Dual ℂ _) := by
  rw [A, ModularCurve.coe_periodLatticeHeckeEnd_apply (ModularCurve.periodLatticeHeckeStable M),
    ModularCurve.dualHeckeRep_apply, ModularCurve.cuspHeckeRep_heckeGen,
    ModularCurve.cuspHeckeGen_of_not_dvd M ⟨ℓ.1, ℓ.2.1⟩ ℓ.2.2.1]
  rfl

def AU {q : ℕ} (hq : q.Prime) : Module.End ℤ (ModularCurve.periodLattice M) :=
  ModularCurve.periodLatticeHeckeEnd M (ModularCurve.heckeGen ⟨q, hq⟩)

def DU {q : ℕ} (hqM : q ∣ M) :
    Module.End ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) :=
  (CuspForm.heckeULin (N := M) 2 hqM).dualMap

theorem coe_AU_apply {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (x : ModularCurve.periodLattice M) :
    ((AU hq x : ModularCurve.periodLattice M) : Module.Dual ℂ _) = DU hqM (x : Module.Dual ℂ _) := by
  rw [AU, ModularCurve.coe_periodLatticeHeckeEnd_apply (ModularCurve.periodLatticeHeckeStable M),
    ModularCurve.dualHeckeRep_apply, ModularCurve.cuspHeckeRep_heckeGen,
    ModularCurve.cuspHeckeGen_of_dvd M ⟨q, hq⟩ hqM]
  rfl

def A' (S : Finset ℕ) {q : ℕ} (hq : q.Prime) : Option (I M S) → Module.End ℤ (ModularCurve.periodLattice M)
  | none => AU hq
  | some ℓ => A S ℓ

def D' (S : Finset ℕ) {q : ℕ} (hqM : q ∣ M) :
    Option (I M S) → Module.End ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2))
  | none => DU hqM
  | some ℓ => D S ℓ

theorem coe_A'_apply (S : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) :
    ∀ (i : Option (I M S)) (x : ModularCurve.periodLattice M),
      ((A' S hq i x : ModularCurve.periodLattice M) : Module.Dual ℂ _) =
        D' S hqM i (x : Module.Dual ℂ _)
  | none, x => coe_AU_apply hq hqM x
  | some ℓ, x => coe_A_apply S ℓ x

theorem iInf_D_eq_Edual (S : Finset ℕ) (h : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    (⨅ ℓ : I M S, Module.End.eigenspace (D S ℓ) (qCoeff h ℓ)) = Edual S h := rfl

theorem finrank_iInf_D'_eq_one (S : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    {h : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hh : h.IsNewform)
    (c : Option (I M S) → ℂ) (hcn : c none = qCoeff h q) (hcs : ∀ ℓ, c (some ℓ) = qCoeff h ℓ) :
    Module.finrank ℂ ↥(⨅ i, Module.End.eigenspace (D' S hqM i) (c i)) = 1 := by
  have heq : (⨅ i, Module.End.eigenspace (D' S hqM i) (c i)) = Edual S h := by
    rw [iInf_option]
    show Module.End.eigenspace (DU hqM) (c none) ⊓
        ⨅ ℓ : I M S, Module.End.eigenspace (D S ℓ) (c (some ℓ)) = Edual S h
    rw [hcn, show (⨅ ℓ : I M S, Module.End.eigenspace (D S ℓ) (c (some ℓ))) = Edual S h from
      (iInf_congr fun ℓ => by rw [hcs]).trans (iInf_D_eq_Edual S h)]
    exact inf_eq_right.mpr (Edual_le_eigenspace_U S hh hq hqM)
  rw [heq]
  exact CuspForm.IsNewform.finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one hh S

theorem finrank_iInf_D_eq_one (S : Finset ℕ)
    {h : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hh : h.IsNewform)
    (c : I M S → ℂ) (hcs : ∀ ℓ, c ℓ = qCoeff h ℓ) :
    Module.finrank ℂ ↥(⨅ ℓ, Module.End.eigenspace (D S ℓ) (c ℓ)) = 1 := by
  rw [show (⨅ ℓ, Module.End.eigenspace (D S ℓ) (c ℓ)) = Edual S h from
    (iInf_congr fun ℓ => by rw [hcs]).trans (iInf_D_eq_Edual S h)]
  exact CuspForm.IsNewform.finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one hh S

variable {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}

theorem finrank_field_T (S : Finset ℕ) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = qCoeff g ℓ)
    (K : Type) [Field K] [CharZero K] (φ : chig.range →+* K) :
    Module.finrank K ↥(⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K)
      (φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)))) = 2 := by
  obtain ⟨ρ, hρ⟩ := CuspForm.exists_qCoeff_conj M 2
  have hgc : (ρ g).IsNewform := isNewform_of_qCoeff_eq_conj hg (hρ g)
  have hcs : ∀ ℓ : I M S,
      ((chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2) : chig.range) : ℂ) =
        qCoeff g ℓ := fun ℓ => by
    rw [RingHom.coe_rangeRestrict, hchig ℓ ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2]
  exact finrank_field_of_complex_counts S chig (A S) (D S) (coe_A_apply S)
    (fun ℓ => chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2))
    (finrank_iInf_D_eq_one S hg
      (fun ℓ : I M S => ((chig.rangeRestrict
        (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2) : chig.range) : ℂ)) hcs)
    (finrank_iInf_D_eq_one S hgc
      (fun ℓ : I M S => starRingEnd ℂ ((chig.rangeRestrict
        (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2) : chig.range) : ℂ))
      fun ℓ => by beta_reduce; rw [hcs, hρ]) K φ

theorem finrank_field_UT (S : Finset ℕ) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = qCoeff g ℓ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (a : ℤ) (ha : qCoeff g q = (a : ℂ))
    (K : Type) [Field K] [CharZero K] (φ : chig.range →+* K)
    (cR : Option (I M S) → chig.range) (hcRn : cR none = (a : chig.range))
    (hcRs : ∀ ℓ : I M S, cR (some ℓ) = chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)) :
    Module.finrank K ↥(⨅ i, Module.End.eigenspace ((A' S hq i).baseChange K) (φ (cR i))) = 2 := by
  obtain ⟨ρ, hρ⟩ := CuspForm.exists_qCoeff_conj M 2
  have hgc : (ρ g).IsNewform := isNewform_of_qCoeff_eq_conj hg (hρ g)
  have hcs : ∀ ℓ : I M S, ((cR (some ℓ) : chig.range) : ℂ) = qCoeff g ℓ := fun ℓ => by
    rw [hcRs, RingHom.coe_rangeRestrict, hchig ℓ ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2]
  have hcn : ((cR none : chig.range) : ℂ) = qCoeff g q := by
    rw [hcRn, ha, SubringClass.coe_intCast]
  exact finrank_field_of_complex_counts S chig (A' S hq) (D' S hqM) (coe_A'_apply S hq hqM) cR
    (finrank_iInf_D'_eq_one S hq hqM hg (fun i => ((cR i : chig.range) : ℂ)) hcn hcs)
    (finrank_iInf_D'_eq_one S hq hqM hgc (fun i => starRingEnd ℂ ((cR i : chig.range) : ℂ))
      (by beta_reduce; rw [hcn, hρ]) fun ℓ => by beta_reduce; rw [hcs, hρ]) K φ

theorem AU_baseChange_eq_smul (S : Finset ℕ) (hg : g.IsNewform)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = qCoeff g ℓ)
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (a : ℤ) (ha : qCoeff g q = (a : ℂ))
    (K : Type) [Field K] [CharZero K] (φ : chig.range →+* K)
    (w : K ⊗[ℤ] ModularCurve.periodLattice M)
    (hw : ∀ ℓ : I M S, (A S ℓ).baseChange K w =
      φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)) • w) :
    (AU hq).baseChange K w = (a : K) • w := by
  classical
  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top M
  haveI : Module.Finite K (K ⊗[ℤ] ModularCurve.periodLattice M) :=
    Module.Finite.of_basis (b.baseChange K)
  have h2T := finrank_field_T S hg chig hchig K φ
  have h2UT := finrank_field_UT S hg chig hchig hq hqM a ha K φ
    (fun i => i.elim (a : chig.range)
      (fun ℓ : I M S => chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)))
    rfl (fun _ => rfl)

  have hEq : (Module.End.eigenspace ((AU hq).baseChange K) ((a : K)) ⊓
      ⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K)
        (φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)))) =
      ⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K)
        (φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2))) := by
    apply Submodule.eq_of_le_of_finrank_eq inf_le_right
    refine Eq.trans ?_ h2T.symm
    refine Eq.trans ?_ h2UT
    rw [iInf_option]
    show _ = Module.finrank K
      ↥(Module.End.eigenspace ((AU hq).baseChange K) (φ ((a : chig.range))) ⊓
        ⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K)
          (φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2))))
    rw [map_intCast]
  have hwT : w ∈ ⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K)
      (φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2))) := by
    rw [Submodule.mem_iInf]
    intro ℓ
    rw [Module.End.mem_eigenspace_iff]
    exact hw ℓ
  rw [← hEq] at hwT
  exact Module.End.mem_eigenspace_iff.mp hwT.1

end PeriodSide

section Abstract

theorem exists_transport {p : ℕ} [Fact p.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
    [SMul ModularCurve.HeckeAlg T] {Λ : Type} [AddCommGroup Λ]
    (O'' : Type) [CommRing O''] [Algebra ℤ_[p] O''] (K : Type) [Field K] [Algebra O'' K]
    (ε : T ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] Λ) (plHE : ModularCurve.HeckeAlg → Module.End ℤ Λ)
    (hεx : ∀ (t : ModularCurve.HeckeAlg) (x : T), ε (t • x) = (plHE t).baseChange ℤ_[p] (ε x))
    (TM : ModularCurve.HeckeAlg →+* Module.End O'' (O'' ⊗[ℤ_[p]] T))
    (hT : ∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : T), TM t (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] (t • x)) :
    ∃ Θ : (K ⊗[O''] (O'' ⊗[ℤ_[p]] T)) ≃ₗ[K] K ⊗[ℤ] Λ,
      ∀ (t : ModularCurve.HeckeAlg) (v : K ⊗[O''] (O'' ⊗[ℤ_[p]] T)),
        Θ ((TM t).baseChange K v) = (plHE t).baseChange K (Θ v) := by
  let s12 : (O'' ⊗[ℤ_[p]] T) ≃ₗ[O''] (O'' ⊗[ℤ] Λ) :=
    (ε.baseChange ℤ_[p] O'' _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[p] O'' O'' Λ)
  have hs12 : ∀ (a : O'') (x : T), s12 (a ⊗ₜ[ℤ_[p]] x) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℤ_[p] O'' O'' Λ (a ⊗ₜ[ℤ_[p]] ε x) :=
    fun a x => by rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  have h12 : ∀ (t : ModularCurve.HeckeAlg) (w : O'' ⊗[ℤ_[p]] T),
      s12 (TM t w) = (plHE t).baseChange O'' (s12 w) := by
    intro t w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      rw [hT, hs12, hs12, hεx]
      exact cancel_nat ℤ ℤ_[p] O'' (plHE t) a (ε x)
    | add y z hy hz => simp only [map_add, hy, hz]
  let Θ : (K ⊗[O''] (O'' ⊗[ℤ_[p]] T)) ≃ₗ[K] K ⊗[ℤ] Λ :=
    (s12.baseChange O'' K _ _).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ O'' K K Λ)
  have hΘ : ∀ (k : K) (w : O'' ⊗[ℤ_[p]] T), Θ (k ⊗ₜ[O''] w) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ O'' K K Λ (k ⊗ₜ[O''] s12 w) :=
    fun k w => by rw [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  refine ⟨Θ, fun t v => ?_⟩
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul k w =>
    rw [LinearMap.baseChange_tmul, hΘ, hΘ, h12]
    exact cancel_nat ℤ O'' K (plHE t) k (s12 w)
  | add y z hy hz => simp only [map_add, hy, hz]

theorem transport_smul {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (Θ : V ≃ₗ[K] W) {M : ℕ} (S : Finset ℕ)
    (X : Nat.Primes → Module.End K V) (Y : Nat.Primes → Module.End K W)
    (hXY : ∀ (q : Nat.Primes) (v : V), Θ (X q v) = Y q (Θ v))
    (ψ : I M S → K) (q₀ : Nat.Primes) (a : K)
    (hW : ∀ w : W, (∀ ℓ : I M S, Y ⟨ℓ.1, ℓ.2.1⟩ w = ψ ℓ • w) → Y q₀ w = a • w)
    (v : V) (hv : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))),
        X ⟨ℓ, hℓ⟩ v = ψ ⟨ℓ, hℓ, hℓN, hℓS⟩ • v) :
    X q₀ v = a • v := by
  apply Θ.injective
  rw [hXY, map_smul]
  apply hW
  rintro ⟨ℓ, hℓ, hℓN, hℓS⟩
  have hh := congrArg Θ (hv ℓ hℓ hℓN hℓS)
  rw [hXY, map_smul] at hh
  exact hh

end Abstract

end HeckeUEigenspaceTate

open HeckeUEigenspaceTate in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [Fact lam.Prime]
    (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (O'' : Type) [CommRing O''] [Algebra ℤ_[lam] O'']
    (K : Type) [Field K] [CharZero K] [Algebra O'' K]
    (φ : chig.range →+* K)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) :
    letI := ModularCurve.heckeModuleBar M
    ∀ [Module ℤ_[lam] (ModularCurve.TateModule lam (ModularCurve.JZero M))]
      (_hsmul : ∀ (a : ℤ_[lam]) (x : ModularCurve.TateModule lam (ModularCurve.JZero M)) (n : ℕ),
        ((a • x : ModularCurve.TateModule lam (ModularCurve.JZero M)) : ℕ → ModularCurve.JZero M) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → ModularCurve.JZero M) n)
      (TM : ModularCurve.HeckeAlg →+* Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M)))
      (_hT : ∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : ModularCurve.TateModule lam (ModularCurve.JZero M)),
        TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x)),
    ∃ a : ℤ, (a = 0 ∨ a = 1 ∨ a = -1) ∧ ModularFormClass.qCoeff g q = (a : ℂ) ∧
      ∀ v : K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M)),
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))),
            (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K v =
              φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • v) →
        (TM (ModularCurve.heckeGen ⟨q, hq⟩)).baseChange K v = (a : K) • v := by
  letI := ModularCurve.heckeModuleBar M
  intro inst hsmul TM hT
  obtain ⟨a, ha3, ha⟩ := exists_int_qCoeff_eq hg q hq hqM
  refine ⟨a, ha3, ha, fun v hv => ?_⟩

  obtain ⟨e, he⟩ :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
      M lam (ModularCurve.heckeInputsAll M) (ModularCurve.heckeOperatorsCommuteBar M)
      (ModularCurve.periodLatticeHeckeStable M)
  have hεx : ∀ (t : ModularCurve.HeckeAlg) (x : ModularCurve.TateModule lam (ModularCurve.JZero M)),
      ((β hsmul).trans e) (t • x) =
        (ModularCurve.periodLatticeHeckeEnd M t).baseChange ℤ_[lam] (((β hsmul).trans e) x) := by
    intro t x
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, β_hecke, he]

  obtain ⟨Θ, hΘ⟩ := exists_transport (p := lam)
    (T := ModularCurve.TateModule lam (ModularCurve.JZero M)) (Λ := ModularCurve.periodLattice M)
    O'' K ((β hsmul).trans e) (fun t => ModularCurve.periodLatticeHeckeEnd M t) hεx TM hT
  exact transport_smul Θ S (fun r => (TM (ModularCurve.heckeGen r)).baseChange K)
    (fun r => (ModularCurve.periodLatticeHeckeEnd M (ModularCurve.heckeGen r)).baseChange K)
    (fun r v => hΘ (ModularCurve.heckeGen r) v)
    (fun ℓ => φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)))
    ⟨q, hq⟩ (a : K)
    (fun w hw => AU_baseChange_eq_smul S hg chig hchig hq hqM a ha K φ w hw) v hv

end
end S_CuspForm_IsNewform_heckeU_eq_intCast_smul_of_mem_heckeEigenspace_tateModule_jZero
end P2MW
export P2MW.S_CuspForm_IsNewform_heckeU_eq_intCast_smul_of_mem_heckeEigenspace_tateModule_jZero (solution)

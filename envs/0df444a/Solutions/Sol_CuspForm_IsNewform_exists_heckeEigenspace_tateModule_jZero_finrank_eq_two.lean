-- Prove2me | solution 1 for CuspForm.IsNewform.exists_heckeEigenspace_tateModule_jZero_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d18cdb5d-427d-5f93-8b58-ce4b3c6017ed

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_exists_heckeEigenspace_tateModule_jZero_finrank_eq_two
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open scoped TensorProduct

namespace HeckeEigenspaceTate

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

theorem finrank_iInf_eigenspace_conj {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V]
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

theorem finrank_iInf_eigenspace_conj' {R : Type*} [Field R] {V V' : Type*} [AddCommGroup V]
    [AddCommGroup V'] [Module R V] [Module R V'] (e : V ≃ₗ[R] V') {ι : Type*}
    (f : ι → Module.End R V) (f' : ι → Module.End R V')
    (h : ∀ i, e.toLinearMap ∘ₗ f i = f' i ∘ₗ e.toLinearMap) (μ : ι → R) :
    Module.finrank R ↥(⨅ i, Module.End.eigenspace (f' i) (μ i)) =
      Module.finrank R ↥(⨅ i, Module.End.eigenspace (f i) (μ i)) := by
  rw [finrank_iInf_eigenspace_conj e f f' h μ, LinearEquiv.finrank_map_eq]

end Transport

section Integral

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

end Integral

section Conj

open ModularFormClass

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

end Conj

section RealBasis

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

end RealBasis

section PeriodSide

open ModularFormClass

variable {M : ℕ} [NeZero M]

abbrev I (M : ℕ) (S : Finset ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S}

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

theorem finrank_complex (S : Finset ℕ) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNewform) :
    Module.finrank ℂ ↥(⨅ ℓ : I M S,
      Module.End.eigenspace ((A S ℓ).baseChange ℂ) (qCoeff g ℓ)) = 2 := by
  obtain ⟨n, b, hli, hsp⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top M
  rw [Module.End.finrank_iInf_eigenspace_baseChange_complex_eq_add (ModularCurve.periodLattice M) b
    (hli_of_linearIndependent b hli) (hsp_of_span_eq_top b hsp) (D S) (A S) (coe_A_apply S)
    (fun ℓ : I M S => qCoeff g ℓ)]
  have h1 : Module.finrank ℂ ↥(⨅ ℓ : I M S, Module.End.eigenspace (D S ℓ) (qCoeff g ℓ)) = 1 :=
    CuspForm.IsNewform.finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one hg S
  obtain ⟨ρ, hρ⟩ := CuspForm.exists_qCoeff_conj M 2
  have hgc : (ρ g).IsNewform := isNewform_of_qCoeff_eq_conj hg (hρ g)
  have heq : (⨅ ℓ : I M S, Module.End.eigenspace (D S ℓ) (starRingEnd ℂ (qCoeff g ℓ))) =
      ⨅ ℓ : I M S, Module.End.eigenspace (D S ℓ) (qCoeff (ρ g) ℓ) :=
    iInf_congr fun ℓ => by rw [hρ]
  have h2 : Module.finrank ℂ ↥(⨅ ℓ : I M S, Module.End.eigenspace (D S ℓ) (qCoeff (ρ g) ℓ)) = 1 :=
    CuspForm.IsNewform.finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one hgc S
  rw [h1, heq, h2]

theorem isIntegral_range (S : Finset ℕ) (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ) :
    Algebra.IsIntegral ℤ chig.range := by
  haveI := CuspForm.moduleFinite_heckeAlgebra_two M (↑S : Set ℕ)
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := RingHom.rangeRestrict_surjective chig x
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) y).map chig.rangeRestrict.toIntAlgHom

theorem finrank_field (S : Finset ℕ) {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNewform) (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = qCoeff g ℓ)
    (K : Type) [Field K] [CharZero K] (φ : chig.range →+* K) :
    Module.finrank K ↥(⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K)
      (φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)))) = 2 := by
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
  let ι : Fr ≃+* F := RingEquiv.ofBijective σC.rangeRestrictField hσC
  let τK : F →+* K := σK.comp ι.symm.toRingHom
  letI : Algebra F K := τK.toAlgebra
  obtain ⟨n, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top M
  haveI : Module.Finite F (F ⊗[ℤ] ModularCurve.periodLattice M) :=
    Module.Finite.of_basis (b.baseChange F)
  let TF : I M S → Module.End F (F ⊗[ℤ] ModularCurve.periodLattice M) :=
    fun ℓ => (A S ℓ).baseChange F
  let cR : I M S → chig.range :=
    fun ℓ => chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)
  let cF : I M S → F := fun ℓ => ι (algebraMap chig.range Fr (cR ℓ))
  have hK := Module.End.finrank_iInf_eigenspace_baseChange_eq F K TF cF
  have hC := Module.End.finrank_iInf_eigenspace_baseChange_eq F ℂ TF cF

  have hcK : ∀ ℓ, algebraMap F K (cF ℓ) = φ (cR ℓ) := fun ℓ => by
    show σK (ι.symm (ι (algebraMap _ Fr (cR ℓ)))) = φ (cR ℓ)
    rw [RingEquiv.symm_apply_apply]
    exact IsFractionRing.lift_algebraMap hφ (cR ℓ)
  have hcC : ∀ ℓ, algebraMap F ℂ (cF ℓ) = qCoeff g ℓ := fun ℓ => by
    show ((σC.rangeRestrictField (algebraMap _ Fr (cR ℓ)) : F) : ℂ) = qCoeff g ℓ
    rw [RingHom.coe_rangeRestrictField, IsFractionRing.lift_algebraMap]
    show ((chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2) : chig.range) : ℂ) = _
    rw [RingHom.coe_rangeRestrict, hchig ℓ ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2]

  have hTK : Module.finrank K ↥(⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K)
      (φ (cR ℓ))) = Module.finrank K ↥(⨅ ℓ : I M S,
        Module.End.eigenspace ((TF ℓ).baseChange K) (algebraMap F K (cF ℓ))) := by
    rw [show (⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K) (φ (cR ℓ))) =
        ⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange K) (algebraMap F K (cF ℓ)) from
      iInf_congr fun ℓ => by rw [hcK]]
    exact finrank_iInf_eigenspace_conj'
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ F K K (ModularCurve.periodLattice M))
      (fun ℓ => (TF ℓ).baseChange K) (fun ℓ => (A S ℓ).baseChange K)
      (fun ℓ => cancel_conj ℤ F K (A S ℓ)) (fun ℓ => algebraMap F K (cF ℓ))
  have hTC : Module.finrank ℂ ↥(⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange ℂ)
      (qCoeff g ℓ)) = Module.finrank ℂ ↥(⨅ ℓ : I M S,
        Module.End.eigenspace ((TF ℓ).baseChange ℂ) (algebraMap F ℂ (cF ℓ))) := by
    rw [show (⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange ℂ) (qCoeff g ℓ)) =
        ⨅ ℓ : I M S, Module.End.eigenspace ((A S ℓ).baseChange ℂ) (algebraMap F ℂ (cF ℓ)) from
      iInf_congr fun ℓ => by rw [hcC]]
    exact finrank_iInf_eigenspace_conj'
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ F ℂ ℂ (ModularCurve.periodLattice M))
      (fun ℓ => (TF ℓ).baseChange ℂ) (fun ℓ => (A S ℓ).baseChange ℂ)
      (fun ℓ => cancel_conj ℤ F ℂ (A S ℓ)) (fun ℓ => algebraMap F ℂ (cF ℓ))
  rw [hTK, hK, ← hC, ← hTC]
  exact finrank_complex S hg

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

theorem package {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (Θ : V ≃ₗ[K] W) {M : ℕ} (S : Finset ℕ)
    (X : Nat.Primes → Module.End K V) (Y : Nat.Primes → Module.End K W)
    (hXY : ∀ (q : Nat.Primes) (v : V), Θ (X q v) = Y q (Θ v))
    (ψ : I M S → K)
    (hfin : Module.finrank K ↥(⨅ ℓ : I M S, Module.End.eigenspace (Y ⟨ℓ.1, ℓ.2.1⟩) (ψ ℓ)) = 2) :
    ∃ E : Submodule K V, Module.finrank K E = 2 ∧
      ∀ v : V, v ∈ E ↔ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))),
        X ⟨ℓ, hℓ⟩ v = ψ ⟨ℓ, hℓ, hℓN, hℓS⟩ • v := by
  refine ⟨(⨅ ℓ : I M S, Module.End.eigenspace (Y ⟨ℓ.1, ℓ.2.1⟩) (ψ ℓ)).map Θ.symm.toLinearMap,
    ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hfin
  · intro v
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    constructor
    · intro h ℓ hℓ hℓN hℓS
      have hh := h ⟨ℓ, hℓ, hℓN, hℓS⟩
      apply Θ.injective
      rw [map_smul, hXY]
      exact hh
    · rintro h ⟨ℓ, hℓ, hℓN, hℓS⟩
      have hh := congrArg Θ (h ℓ hℓ hℓN hℓS)
      rw [hXY, map_smul] at hh
      exact hh

end Abstract

end HeckeEigenspaceTate

open HeckeEigenspaceTate in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [Fact lam.Prime]
    (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (O'' : Type) [CommRing O''] [Algebra ℤ_[lam] O'']
    (K : Type) [Field K] [CharZero K] [Algebra O'' K]
    (φ : chig.range →+* K) :
    letI := ModularCurve.heckeModuleBar M
    ∀ [Module ℤ_[lam] (ModularCurve.TateModule lam (ModularCurve.JZero M))]
      (_hsmul : ∀ (a : ℤ_[lam]) (x : ModularCurve.TateModule lam (ModularCurve.JZero M)) (n : ℕ),
        ((a • x : ModularCurve.TateModule lam (ModularCurve.JZero M)) : ℕ → ModularCurve.JZero M) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → ModularCurve.JZero M) n)
      (TM : ModularCurve.HeckeAlg →+*
        Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M)))
      (_hT : ∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : ModularCurve.TateModule lam (ModularCurve.JZero M)),
        TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x)),
    ∃ E : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M))),
      Module.finrank K E = 2 ∧
      ∀ v : K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M)),
        v ∈ E ↔
          ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))),
            (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K v =
              φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • v := by
  letI := ModularCurve.heckeModuleBar M
  intro inst hsmul TM hT

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
  exact package Θ S (fun q => (TM (ModularCurve.heckeGen q)).baseChange K)
    (fun q => (ModularCurve.periodLatticeHeckeEnd M (ModularCurve.heckeGen q)).baseChange K)
    (fun q v => hΘ (ModularCurve.heckeGen q) v)
    (fun ℓ => φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T ℓ.2.1 ℓ.2.2.1 ℓ.2.2.2)))
    (finrank_field S hg chig hchig K φ)

end
end S_CuspForm_IsNewform_exists_heckeEigenspace_tateModule_jZero_finrank_eq_two
end P2MW
export P2MW.S_CuspForm_IsNewform_exists_heckeEigenspace_tateModule_jZero_finrank_eq_two (solution)

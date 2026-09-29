-- Prove2me | solution 1 for CuspForm.IsNewform.frobeniusTrace_of_eigenPlane_tateModule_jZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ca1f4d34-7aa6-5ad5-a1ee-265bf8739524

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_ModularCurve_rationalRankTwoCyclotomic_family
import Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jZero
import Theorems.Thm_ModularCurve_rep_tateModule_jZero_comm
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_CuspForm_IsNewform_exists_heckeEigenspace_tateModule_jZero_finrank_eq_two
import Theorems.Thm_LinearMap_charpoly_of_finrank_eq_two
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.NoncommRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_frobeniusTrace_of_eigenPlane_tateModule_jZero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
open ModularCurve TensorProduct
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

noncomputable section

namespace OrdPtFrobTrace

open TensorProduct Polynomial

section Scalars

theorem padicInt_ringHom_injective {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharZero K]
    (ι : ℤ_[p] →+* K) : Function.Injective ι := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast, mul_eq_zero] at ha
  rcases ha with h | h
  · exact (Units.map (ι : ℤ_[p] →* K) (PadicInt.unitCoeff h0)).ne_zero h
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h

end Scalars

section Transport

theorem exists_transport₂ {p : ℕ} [Fact p.Prime] {T T' : Type*} [AddCommGroup T] [Module ℤ_[p] T]
    [AddCommGroup T'] [Module ℤ_[p] T']
    (O'' : Type*) [CommRing O''] [Algebra ℤ_[p] O''] (K : Type*) [Field K] [Algebra O'' K]
    [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] O'' K] [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (ε : T ≃ₗ[ℤ_[p]] T') :
    ∃ Θ : (K ⊗[O''] (O'' ⊗[ℤ_[p]] T)) ≃ₗ[K] K ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] T'),
      ∀ (Φ : Module.End O'' (O'' ⊗[ℤ_[p]] T)) (f : Module.End ℤ_[p] T'),
        (∀ (a : O'') (x : T), Φ (a ⊗ₜ[ℤ_[p]] x) = a ⊗ₜ[ℤ_[p]] ε.symm (f (ε x))) →
        ∀ v, Θ (Φ.baseChange K v) = ((f.baseChange ℚ_[p]).baseChange K) (Θ v) := by
  let Θ : (K ⊗[O''] (O'' ⊗[ℤ_[p]] T)) ≃ₗ[K] K ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] T') :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[p] O'' K K T).trans
      ((ε.baseChange ℤ_[p] K T T').trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[p] ℚ_[p] K K T').symm)
  have hΘ : ∀ (k : K) (a : O'') (x : T),
      Θ (k ⊗ₜ[O''] (a ⊗ₜ[ℤ_[p]] x)) = (a • k) ⊗ₜ[ℚ_[p]] ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] ε x) :=
    fun k a x => rfl
  refine ⟨Θ, fun Φ f hΦ v => ?_⟩
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul k w =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | tmul a x =>
      rw [LinearMap.baseChange_tmul, hΦ, hΘ, hΘ, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        LinearEquiv.apply_symm_apply]
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | add y z hy hz => simp only [map_add, hy, hz]

end Transport

section BasisTwo

variable {R : Type*} [Field R] {V : Type*} [AddCommGroup V] [Module R V]
  (A : Subalgebra R (Module.End R V)) (b : Module.Basis (Fin 2) A V)

theorem subalg_smul_def (x : A) (v : V) : x • v = (x : Module.End R V) v := rfl

def evalAt (v₀ : V) : A →ₗ[R] V where
  toFun x := (x : Module.End R V) v₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem evalAt_apply (v₀ : V) (x : A) : evalAt A v₀ x = (x : Module.End R V) v₀ := rfl

def Φ : (A × A) →ₗ[R] V := (evalAt A (b 0)).coprod (evalAt A (b 1))

theorem Φ_apply (x : A × A) :
    Φ A b x = (x.1 : Module.End R V) (b 0) + (x.2 : Module.End R V) (b 1) := rfl

theorem Φ_bijective : Function.Bijective (Φ A b) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨x₀, x₁⟩ h
    have hli := Fintype.linearIndependent_iff.mp b.linearIndependent ![x₀, x₁] (by
      rw [Fin.sum_univ_two]
      exact h)
    have h0 := hli 0
    have h1 := hli 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [h0, h1]
    rfl
  · intro v
    refine ⟨(b.repr v 0, b.repr v 1), ?_⟩
    conv_rhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two]
    rfl

noncomputable def ΦE : (A × A) ≃ₗ[R] V := LinearEquiv.ofBijective (Φ A b) (Φ_bijective A b)

@[scoped simp] theorem ΦE_apply (x : A × A) :
    ΦE A b x = (x.1 : Module.End R V) (b 0) + (x.2 : Module.End R V) (b 1) := rfl

variable (K : Type*) [Field K] [Algebra R K]

noncomputable def ΦK : ((K ⊗[R] A) × (K ⊗[R] A)) ≃ₗ[K] K ⊗[R] V :=
  (TensorProduct.prodRight R K K A A).symm.trans ((ΦE A b).baseChange R K _ _)

theorem ΦK_eq_coprod : (ΦK A b K).toLinearMap =
    ((evalAt A (b 0)).baseChange K).coprod ((evalAt A (b 1)).baseChange K) := by
  apply LinearMap.prod_ext
  · apply TensorProduct.AlgebraTensorModule.ext
    intro k x
    rw [LinearMap.coprod_inl, LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.inl_apply, show ((k ⊗ₜ[R] x, 0) : (K ⊗[R] A) × (K ⊗[R] A)) =
        (k ⊗ₜ[R] x, k ⊗ₜ[R] (0 : A)) by rw [tmul_zero]]
    show ((ΦE A b).baseChange R K _ _) ((TensorProduct.prodRight R K K A A).symm (k ⊗ₜ x, k ⊗ₜ 0)) = _
    rw [TensorProduct.prodRight_symm_tmul, LinearEquiv.baseChange_tmul, ΦE_apply, evalAt_apply]
    show k ⊗ₜ[R] ((x : Module.End R V) (b 0) + (0 : Module.End R V) (b 1)) = _
    rw [LinearMap.zero_apply, add_zero]
  · apply TensorProduct.AlgebraTensorModule.ext
    intro k x
    rw [LinearMap.coprod_inr, LinearMap.baseChange_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.inr_apply, show ((0, k ⊗ₜ[R] x) : (K ⊗[R] A) × (K ⊗[R] A)) =
        (k ⊗ₜ[R] (0 : A), k ⊗ₜ[R] x) by rw [tmul_zero]]
    show ((ΦE A b).baseChange R K _ _) ((TensorProduct.prodRight R K K A A).symm (k ⊗ₜ 0, k ⊗ₜ x)) = _
    rw [TensorProduct.prodRight_symm_tmul, LinearEquiv.baseChange_tmul, ΦE_apply, evalAt_apply]
    show k ⊗ₜ[R] ((0 : Module.End R V) (b 0) + (x : Module.End R V) (b 1)) = _
    rw [LinearMap.zero_apply, zero_add]

theorem ΦK_apply (y₀ y₁ : K ⊗[R] A) :
    ΦK A b K (y₀, y₁) = (evalAt A (b 0)).baseChange K y₀ + (evalAt A (b 1)).baseChange K y₁ := by
  have h := congrArg (fun f : ((K ⊗[R] A) × (K ⊗[R] A)) →ₗ[K] K ⊗[R] V => f (y₀, y₁)) (ΦK_eq_coprod A b K)
  simpa using h

noncomputable def Lop (x : A) : Module.End K (K ⊗[R] A) := (LinearMap.mulLeft R x).baseChange K
noncomputable def Rop (c : A) : Module.End K (K ⊗[R] A) := (LinearMap.mulRight R c).baseChange K

@[scoped simp] theorem Lop_tmul (x : A) (k : K) (z : A) : Lop A K x (k ⊗ₜ[R] z) = k ⊗ₜ[R] (x * z) := rfl
@[scoped simp] theorem Rop_tmul (c : A) (k : K) (z : A) : Rop A K c (k ⊗ₜ[R] z) = k ⊗ₜ[R] (z * c) := rfl

theorem Lop_Rop_comm (x c : A) (y : K ⊗[R] A) : Lop A K x (Rop A K c y) = Rop A K c (Lop A K x y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul k z => rw [Rop_tmul, Lop_tmul, Lop_tmul, Rop_tmul, mul_assoc]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem Rop_one : Rop A K 1 = 1 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro k z
  rw [Rop_tmul, mul_one]
  rfl

theorem Rop_mul (c d : A) : Rop A K (c * d) = Rop A K d * Rop A K c := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro k z
  rw [Rop_tmul, Module.End.mul_apply, Rop_tmul, Rop_tmul, mul_assoc]

theorem Rop_add (c d : A) : Rop A K (c + d) = Rop A K c + Rop A K d := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro k z
  rw [Rop_tmul, LinearMap.add_apply, Rop_tmul, Rop_tmul, mul_add, tmul_add]

theorem Rop_algebraMap (r : R) (y : K ⊗[R] A) : Rop A K (algebraMap R A r) y = algebraMap R K r • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul k z =>
    rw [Rop_tmul, ← Algebra.commutes, ← Algebra.smul_def, tmul_smul, algebraMap_smul]
  | add y z hy hz => simp only [map_add, hy, hz, smul_add]

theorem op_ΦK (x : A) (y₀ y₁ : K ⊗[R] A) :
    ((x : Module.End R V).baseChange K) (ΦK A b K (y₀, y₁)) = ΦK A b K (Lop A K x y₀, Lop A K x y₁) := by
  have key : ∀ (v₀ : V) (y : K ⊗[R] A),
      ((x : Module.End R V).baseChange K) ((evalAt A v₀).baseChange K y) =
        (evalAt A v₀).baseChange K (Lop A K x y) := by
    intro v₀ y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul k z => rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Lop_tmul,
        LinearMap.baseChange_tmul, evalAt_apply, evalAt_apply]; rfl
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [ΦK_apply, ΦK_apply, map_add, key, key]

theorem comm_ΦK (s : Module.End R V) (hs : ∀ x : A, (x : Module.End R V) * s = s * x)
    (c : Fin 2 → Fin 2 → A)
    (hc : ∀ j : Fin 2, s (b j) = (c j 0 : Module.End R V) (b 0) + (c j 1 : Module.End R V) (b 1))
    (y₀ y₁ : K ⊗[R] A) :
    (s.baseChange K) (ΦK A b K (y₀, y₁)) =
      ΦK A b K (Rop A K (c 0 0) y₀ + Rop A K (c 1 0) y₁, Rop A K (c 0 1) y₀ + Rop A K (c 1 1) y₁) := by
  have key : ∀ (j : Fin 2) (y : K ⊗[R] A),
      (s.baseChange K) ((evalAt A (b j)).baseChange K y) =
        (evalAt A (b 0)).baseChange K (Rop A K (c j 0) y) + (evalAt A (b 1)).baseChange K (Rop A K (c j 1) y) := by
    intro j y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul k z =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, evalAt_apply, Rop_tmul, Rop_tmul,
        LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, evalAt_apply, evalAt_apply, ← tmul_add]
      congr 1
      rw [← Module.End.mul_apply, ← hs, Module.End.mul_apply, hc, map_add]
      rfl
    | add y z hy hz => simp only [map_add, hy, hz]; abel
  rw [ΦK_apply, ΦK_apply, map_add, key, key, map_add, map_add]
  abel

variable {ι : Type*} (t : ι → A) (a : ι → K)

noncomputable def Nsp : Submodule K (K ⊗[R] A) := ⨅ i, Module.End.eigenspace (Lop A K (t i)) (a i)

noncomputable def EV : Submodule K (K ⊗[R] V) :=
  ⨅ i, Module.End.eigenspace (((t i : A) : Module.End R V).baseChange K) (a i)

theorem mem_Nsp_iff (y : K ⊗[R] A) : y ∈ Nsp A K t a ↔ ∀ i, Lop A K (t i) y = a i • y := by
  simp only [Nsp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem mem_EV_iff (v : K ⊗[R] V) :
    v ∈ EV A K t a ↔ ∀ i, (((t i : A) : Module.End R V).baseChange K) v = a i • v := by
  simp only [EV, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem ΦK_mem_EV_iff (y₀ y₁ : K ⊗[R] A) :
    ΦK A b K (y₀, y₁) ∈ EV A K t a ↔ y₀ ∈ Nsp A K t a ∧ y₁ ∈ Nsp A K t a := by
  rw [mem_EV_iff, mem_Nsp_iff, mem_Nsp_iff, ← forall_and]
  apply forall_congr'
  intro i
  rw [op_ΦK, ← map_smul, (ΦK A b K).injective.eq_iff, Prod.smul_mk, Prod.mk.injEq]

theorem Rop_mem_Nsp (c : A) {y : K ⊗[R] A} (hy : y ∈ Nsp A K t a) : Rop A K c y ∈ Nsp A K t a := by
  rw [mem_Nsp_iff] at hy ⊢
  intro i
  rw [Lop_Rop_comm, hy, map_smul]

theorem comm_mem_EV (s : Module.End R V) (hs : ∀ x : A, (x : Module.End R V) * s = s * x)
    {v : K ⊗[R] V} (hv : v ∈ EV A K t a) : s.baseChange K v ∈ EV A K t a := by
  rw [mem_EV_iff] at hv ⊢
  intro i
  rw [← Module.End.mul_apply, ← LinearMap.baseChange_mul, hs, LinearMap.baseChange_mul,
    Module.End.mul_apply, hv, map_smul]

end BasisTwo

theorem trace_eq_of_quadratic_of_det {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (h2 : Module.finrank K E = 2) (f : Module.End K E) (a ℓ : K)
    (hq : f ^ 2 - algebraMap K (Module.End K E) a * f + algebraMap K (Module.End K E) ℓ = 0)
    (hdet : LinearMap.det f = ℓ) (hℓ : ℓ ≠ 0) :
    LinearMap.trace K E f = a := by
  have hch := LinearMap.aeval_self_charpoly f
  rw [LinearMap.charpoly_of_finrank_eq_two h2, hdet] at hch
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C] at hch
  have h3 : algebraMap K (Module.End K E) (a - LinearMap.trace K E f) * f = 0 := by
    have e : algebraMap K (Module.End K E) (a - LinearMap.trace K E f) * f =
        (f ^ 2 - algebraMap K (Module.End K E) (LinearMap.trace K E f) * f
            + algebraMap K (Module.End K E) ℓ) -
          (f ^ 2 - algebraMap K (Module.End K E) a * f + algebraMap K (Module.End K E) ℓ) := by
      rw [map_sub]; noncomm_ring
    rw [e, hch, hq, sub_zero]
  by_contra hne
  have hne' : a - LinearMap.trace K E f ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hf : f = 0 := by
    have h4 := congrArg (fun g => algebraMap K (Module.End K E) (a - LinearMap.trace K E f)⁻¹ * g) h3
    beta_reduce at h4
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne', map_one, one_mul, mul_zero] at h4
  apply hℓ
  rw [← hdet, hf, LinearMap.det_zero, h2]
  simp


theorem trace_eq_of_quadratic_of_det' {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (E : Submodule K X) [FiniteDimensional K E] (h2 : Module.finrank K E = 2) (f : Module.End K E)
    (a ℓ : K)
    (hq : f ^ 2 - algebraMap K (Module.End K E) a * f + algebraMap K (Module.End K E) ℓ = 0)
    (hdet : LinearMap.det f = ℓ) (hℓ : ℓ ≠ 0) :
    LinearMap.trace K E f = a :=
  trace_eq_of_quadratic_of_det h2 f a ℓ hq hdet hℓ
theorem det_eq_of_basis_two {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (b : Module.Basis (Fin 2) K E) (f : Module.End K E) (m₀₀ m₀₁ m₁₀ m₁₁ : K)
    (h0 : f (b 0) = m₀₀ • b 0 + m₀₁ • b 1) (h1 : f (b 1) = m₁₀ • b 0 + m₁₁ • b 1) :
    LinearMap.det f = m₀₀ * m₁₁ - m₁₀ * m₀₁ := by
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  have r0 : b.repr (f (b 0)) = Finsupp.single 0 m₀₀ + Finsupp.single 1 m₀₁ := by
    rw [h0, map_add, map_smul, map_smul, b.repr_self, b.repr_self, Finsupp.smul_single,
      Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  have r1 : b.repr (f (b 1)) = Finsupp.single 0 m₁₀ + Finsupp.single 1 m₁₁ := by
    rw [h1, map_add, map_smul, map_smul, b.repr_self, b.repr_self, Finsupp.smul_single,
      Finsupp.smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  have e00 : LinearMap.toMatrix b b f 0 0 = m₀₀ := by rw [LinearMap.toMatrix_apply, r0]; simp
  have e10 : LinearMap.toMatrix b b f 1 0 = m₀₁ := by rw [LinearMap.toMatrix_apply, r0]; simp
  have e01 : LinearMap.toMatrix b b f 0 1 = m₁₀ := by rw [LinearMap.toMatrix_apply, r1]; simp
  have e11 : LinearMap.toMatrix b b f 1 1 = m₁₁ := by rw [LinearMap.toMatrix_apply, r1]; simp
  rw [e00, e11, e01, e10]

section LineDet

variable {R : Type*} [Field R] {V : Type*} [AddCommGroup V] [Module R V]
  (A : Subalgebra R (Module.End R V)) (b : Module.Basis (Fin 2) A V)
  (K : Type*) [Field K] [Algebra R K] {ι : Type*} (t : ι → A) (a : ι → K)

def ιl : Nsp A K t a →ₗ[K] EV A K t a where
  toFun y := ⟨ΦK A b K ((y : K ⊗[R] A), 0),
    (ΦK_mem_EV_iff A b K t a _ _).mpr ⟨y.2, Submodule.zero_mem _⟩⟩
  map_add' y z := by
    apply Subtype.ext
    show ΦK A b K (((y : K ⊗[R] A) + z), 0) = ΦK A b K ((y : K ⊗[R] A), 0) + ΦK A b K ((z : K ⊗[R] A), 0)
    rw [← map_add, Prod.mk_add_mk, add_zero]
  map_smul' k y := by
    apply Subtype.ext
    show ΦK A b K ((k • (y : K ⊗[R] A)), 0) = k • ΦK A b K ((y : K ⊗[R] A), 0)
    rw [← map_smul, Prod.smul_mk, smul_zero]

def ιr : Nsp A K t a →ₗ[K] EV A K t a where
  toFun y := ⟨ΦK A b K (0, (y : K ⊗[R] A)),
    (ΦK_mem_EV_iff A b K t a _ _).mpr ⟨Submodule.zero_mem _, y.2⟩⟩
  map_add' y z := by
    apply Subtype.ext
    show ΦK A b K (0, ((y : K ⊗[R] A) + z)) = ΦK A b K (0, (y : K ⊗[R] A)) + ΦK A b K (0, (z : K ⊗[R] A))
    rw [← map_add, Prod.mk_add_mk, add_zero]
  map_smul' k y := by
    apply Subtype.ext
    show ΦK A b K (0, (k • (y : K ⊗[R] A))) = k • ΦK A b K (0, (y : K ⊗[R] A))
    rw [← map_smul, Prod.smul_mk, smul_zero]

theorem ιl_apply_coe (y : Nsp A K t a) :
    ((ιl A b K t a y : EV A K t a) : K ⊗[R] V) = ΦK A b K ((y : K ⊗[R] A), 0) := rfl

theorem ιr_apply_coe (y : Nsp A K t a) :
    ((ιr A b K t a y : EV A K t a) : K ⊗[R] V) = ΦK A b K (0, (y : K ⊗[R] A)) := rfl

theorem ιl_injective : Function.Injective (ιl A b K t a) := fun y z h => by
  have h' := congrArg Subtype.val h
  rw [ιl_apply_coe, ιl_apply_coe] at h'
  exact Subtype.ext (Prod.mk.inj ((ΦK A b K).injective h')).1

theorem ι_injective : Function.Injective ((ιl A b K t a).coprod (ιr A b K t a)) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨y, z⟩ h
  have h' := congrArg Subtype.val h
  rw [LinearMap.coprod_apply, Submodule.coe_add, ιl_apply_coe, ιr_apply_coe, Submodule.coe_zero,
    ← map_add, Prod.mk_add_mk, add_zero, zero_add, (ΦK A b K).map_eq_zero_iff, Prod.mk_eq_zero] at h'
  exact Prod.ext (Subtype.ext h'.1) (Subtype.ext h'.2)

theorem ι_surjective : Function.Surjective ((ιl A b K t a).coprod (ιr A b K t a)) := by
  rintro ⟨v, hv⟩
  have hsurj := (ΦK A b K).surjective v
  obtain ⟨yz, hyz⟩ := hsurj
  obtain ⟨y, z⟩ := yz
  subst hyz
  rw [ΦK_mem_EV_iff] at hv
  refine ⟨(⟨y, hv.1⟩, ⟨z, hv.2⟩), Subtype.ext ?_⟩
  rw [LinearMap.coprod_apply, Submodule.coe_add, ιl_apply_coe, ιr_apply_coe, ← map_add, Prod.mk_add_mk,
    add_zero, zero_add]

theorem exists_character (n₀ : K ⊗[R] A) (hn₀ : n₀ ≠ 0)
    (hline : ∀ c : A, ∃ k : K, Rop A K c n₀ = k • n₀) :
    ∃ ψ : A →* K, (∀ c : A, Rop A K c n₀ = ψ c • n₀) ∧ (∀ c d : A, ψ (c - d) = ψ c - ψ d) ∧
      ∀ r : R, ψ (algebraMap R A r) = algebraMap R K r := by
  choose k hk using hline
  have hinj : ∀ x y : K, x • n₀ = y • n₀ → x = y := fun x y h => smul_left_injective K hn₀ h
  have hmul : ∀ c d : A, k (c * d) = k c * k d := fun c d => by
    apply hinj
    rw [← hk (c * d), Rop_mul, Module.End.mul_apply, hk c, map_smul, hk d, smul_smul, mul_comm]
  have hone : k 1 = 1 := by
    apply hinj
    rw [← hk 1, Rop_one, Module.End.one_apply, one_smul]
  let ψ : A →* K := { toFun := k, map_one' := hone, map_mul' := hmul }
  have hadd : ∀ c d : A, k (c + d) = k c + k d := fun c d => by
    apply hinj
    rw [← hk (c + d), Rop_add, LinearMap.add_apply, hk c, hk d, add_smul]
  refine ⟨ψ, hk, fun c d => ?_, fun r => ?_⟩
  · show k (c - d) = k c - k d
    rw [eq_sub_iff_add_eq, ← hadd, sub_add_cancel]
  · apply hinj
    show k (algebraMap R A r) • n₀ = _
    rw [← hk, Rop_algebraMap]

include b in

theorem exists_line_of_plane (E' : Type*) [AddCommGroup E'] [Module K E'] [FiniteDimensional K E']
    (jE : E' →ₗ[K] K ⊗[R] V) (hj : Function.Injective jE)
    (hjE : ∀ w : E', jE w ∈ EV A K t a) (hEj : ∀ v ∈ EV A K t a, ∃ w : E', jE w = v)
    (h2 : Module.finrank K E' = 2) :
    ∃ n₀ : K ⊗[R] A, n₀ ∈ Nsp A K t a ∧ n₀ ≠ 0 ∧ ∀ y ∈ Nsp A K t a, ∃ k : K, k • n₀ = y := by
  have hrange : LinearMap.range jE = EV A K t a := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact hjE w
    · intro v hv
      have hw := hEj v hv
      obtain ⟨w, hw⟩ := hw
      exact ⟨w, hw⟩
  let eE : E' ≃ₗ[K] EV A K t a := (LinearEquiv.ofInjective jE hj).trans (LinearEquiv.ofEq _ _ hrange)
  haveI : Module.Finite K (EV A K t a) := Module.Finite.equiv eE
  haveI : IsNoetherian K (EV A K t a) := isNoetherian_of_isNoetherianRing_of_finite K (EV A K t a)
  haveI : Module.Finite K (Nsp A K t a) :=
    Module.Finite.of_injective (ιl A b K t a) (ιl_injective A b K t a)
  haveI : Module.Free K (Nsp A K t a) := Module.Free.of_divisionRing K (Nsp A K t a)
  have hdim := ((LinearEquiv.ofBijective _ ⟨ι_injective A b K t a, ι_surjective A b K t a⟩).trans eE.symm).finrank_eq
  rw [Module.finrank_prod, h2] at hdim
  have h1 : Module.finrank K (Nsp A K t a) = 1 := by omega
  have h1' := (finrank_eq_one_iff' (K := K) (V := ↥(Nsp A K t a))).mp h1
  obtain ⟨n₀, hn₀, hgen⟩ := h1'
  refine ⟨n₀, n₀.2, fun h => hn₀ (Subtype.ext h), fun y hy => ?_⟩
  have hk' := hgen ⟨y, hy⟩
  obtain ⟨k, hk⟩ := hk'
  exact ⟨k, congrArg Subtype.val hk⟩

theorem exists_basis_of_plane (E' : Type*) [AddCommGroup E'] [Module K E'] [FiniteDimensional K E']
    (jE : E' →ₗ[K] K ⊗[R] V)
    (hEj : ∀ v ∈ EV A K t a, ∃ w : E', jE w = v)
    (h2 : Module.finrank K E' = 2) (n₀ : K ⊗[R] A) (hn : n₀ ∈ Nsp A K t a) (hn0 : n₀ ≠ 0) :
    ∃ bE : Module.Basis (Fin 2) K E', jE (bE 0) = ΦK A b K (n₀, 0) ∧ jE (bE 1) = ΦK A b K (0, n₀) := by
  have hw0' := hEj _ ((ΦK_mem_EV_iff A b K t a n₀ 0).mpr ⟨hn, Submodule.zero_mem _⟩)
  obtain ⟨w0, hw0⟩ := hw0'
  have hw1' := hEj _ ((ΦK_mem_EV_iff A b K t a 0 n₀).mpr ⟨Submodule.zero_mem _, hn⟩)
  obtain ⟨w1, hw1⟩ := hw1'
  let e : Fin 2 → E' := ![w0, w1]
  have he0 : jE (e 0) = ΦK A b K (n₀, 0) := hw0
  have he1 : jE (e 1) = ΦK A b K (0, n₀) := hw1
  have hli : LinearIndependent K e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_two] at hg
    have hg' := congrArg jE hg
    rw [map_add, map_smul, map_smul, he0, he1, map_zero, ← map_smul, ← map_smul, ← map_add, Prod.smul_mk,
      Prod.smul_mk, smul_zero, smul_zero, Prod.mk_add_mk, add_zero, zero_add, (ΦK A b K).map_eq_zero_iff,
      Prod.mk_eq_zero, smul_eq_zero, smul_eq_zero] at hg'
    fin_cases i
    · exact hg'.1.resolve_right hn0
    · exact hg'.2.resolve_right hn0
  have hcard : Fintype.card (Fin 2) = Module.finrank K E' := by rw [h2, Fintype.card_fin]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_, ?_⟩
  · rw [congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) 0, he0]
  · rw [congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) 1, he1]

theorem det_eq_of_plane (E' : Type*) [AddCommGroup E'] [Module K E'] [FiniteDimensional K E']
    (jE : E' →ₗ[K] K ⊗[R] V) (hj : Function.Injective jE)
    (hjE : ∀ w : E', jE w ∈ EV A K t a) (hEj : ∀ v ∈ EV A K t a, ∃ w : E', jE w = v)
    (h2 : Module.finrank K E' = 2)
    (s : Module.End R V) (hs : ∀ x : A, (x : Module.End R V) * s = s * x)
    (c : Fin 2 → Fin 2 → A)
    (hc : ∀ j : Fin 2, s (b j) = (c j 0 : Module.End R V) (b 0) + (c j 1 : Module.End R V) (b 1))
    (r : R) (hdet : c 0 0 * c 1 1 - c 1 0 * c 0 1 = algebraMap R A r)
    (FE : Module.End K E') (hFE : ∀ w : E', jE (FE w) = s.baseChange K (jE w)) :
    LinearMap.det FE = algebraMap R K r := by
  have hl := exists_line_of_plane A b K t a E' jE hj hjE hEj h2
  obtain ⟨n₀, hn, hn0, hgen⟩ := hl
  have hline : ∀ cc : A, ∃ k : K, Rop A K cc n₀ = k • n₀ := fun cc => by
    have hk' := hgen _ (Rop_mem_Nsp A K t a cc hn)
    obtain ⟨k, hk⟩ := hk'
    exact ⟨k, hk.symm⟩
  have hchar := exists_character A K n₀ hn0 hline
  obtain ⟨ψ, hψ, hψsub, hψalg⟩ := hchar
  have hb := exists_basis_of_plane A b K t a E' jE hEj h2 n₀ hn hn0
  obtain ⟨bE, hbE0, hbE1⟩ := hb
  have hF : ∀ (y₀ y₁ : K ⊗[R] A), (s.baseChange K) (ΦK A b K (y₀, y₁)) =
      ΦK A b K (Rop A K (c 0 0) y₀ + Rop A K (c 1 0) y₁, Rop A K (c 0 1) y₀ + Rop A K (c 1 1) y₁) :=
    comm_ΦK A b K s hs c hc
  have h0 : FE (bE 0) = ψ (c 0 0) • bE 0 + ψ (c 0 1) • bE 1 := by
    apply hj
    rw [hFE, map_add, map_smul, map_smul, hbE0, hbE1, hF, map_zero, map_zero,
      add_zero, add_zero, hψ, hψ, ← map_smul, ← map_smul, ← map_add, Prod.smul_mk, Prod.smul_mk, smul_zero,
      smul_zero, Prod.mk_add_mk, add_zero, zero_add]
  have h1e : FE (bE 1) = ψ (c 1 0) • bE 0 + ψ (c 1 1) • bE 1 := by
    apply hj
    rw [hFE, map_add, map_smul, map_smul, hbE0, hbE1, hF, map_zero, map_zero,
      zero_add, zero_add, hψ, hψ, ← map_smul, ← map_smul, ← map_add, Prod.smul_mk, Prod.smul_mk, smul_zero,
      smul_zero, Prod.mk_add_mk, add_zero, zero_add]
  rw [det_eq_of_basis_two (E := E') bE _ _ _ _ _ h0 h1e, ← map_mul, ← map_mul, ← hψsub, hdet, hψalg]

end LineDet

section Quad

theorem quad_baseChange {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] [Module R X]
    (K' : Type*) [CommRing K'] [Algebra R K'] (sv tv : Module.End R X) (r : R) (rK : K')
    (hr : algebraMap R K' r = rK)
    (h : ∀ v : X, sv (sv v) - tv (sv v) + r • v = 0) (v : K' ⊗[R] X) :
    sv.baseChange K' (sv.baseChange K' v) - tv.baseChange K' (sv.baseChange K' v) + rK • v = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero, sub_zero, add_zero]
  | tmul k w =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, ← hr, algebraMap_smul,
      ← tmul_smul, ← tmul_sub, ← tmul_add, h, tmul_zero]
  | add y z hy hz =>
    simp only [map_add, smul_add]
    have e : sv.baseChange K' (sv.baseChange K' y) + sv.baseChange K' (sv.baseChange K' z) -
        (tv.baseChange K' (sv.baseChange K' y) + tv.baseChange K' (sv.baseChange K' z)) +
        (rK • y + rK • z) =
      (sv.baseChange K' (sv.baseChange K' y) - tv.baseChange K' (sv.baseChange K' y) + rK • y) +
      (sv.baseChange K' (sv.baseChange K' z) - tv.baseChange K' (sv.baseChange K' z) + rK • z) := by
      abel
    rw [e, hy, hz, add_zero]

theorem restrict_quadratic {K' : Type*} [Field K'] {X : Type*} [AddCommGroup X] [Module K' X]
    (F T : Module.End K' X) (a r : K') (E : Submodule K' X) (hE : ∀ v ∈ E, F v ∈ E)
    (hq : ∀ v : X, F (F v) - T (F v) + r • v = 0) (hT : ∀ v ∈ E, T (F v) = a • F v) :
    (F.restrict hE) ^ 2 - algebraMap K' (Module.End K' E) a * F.restrict hE
      + algebraMap K' (Module.End K' E) r = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [LinearMap.add_apply, LinearMap.sub_apply, pow_two, Module.End.mul_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.zero_apply, Submodule.coe_zero,
    Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul,
    LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply, ← hT v v.2]
  exact hq v

theorem quad_of_transport {K' : Type*} [Field K'] {L X : Type*} [AddCommGroup L] [Module K' L]
    [AddCommGroup X] [Module K' X] (Θ : L ≃ₗ[K'] X) (F T : Module.End K' L) (FX TX : Module.End K' X)
    (hF : ∀ v, Θ (F v) = FX (Θ v)) (hT : ∀ v, Θ (T v) = TX (Θ v)) (r : K')
    (hq : ∀ x : X, FX (FX x) - TX (FX x) + r • x = 0) (v : L) :
    F (F v) - T (F v) + r • v = 0 := by
  apply Θ.injective
  rw [map_add, map_sub, map_smul, map_zero, hF, hF, hT, hF]
  exact hq (Θ v)

end Quad

section Bridge

variable {p : ℕ} [Fact p.Prime] {J : Type} [AddCommGroup J] [Module ModularCurve.HeckeAlg J]

omit [Fact p.Prime] in
theorem mem_root_of_mem {x : ℕ → J} (hx : x ∈ ModularCurve.TateModule p J) :
    x ∈ _root_.TateModule p J := by
  change ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n
  intro n
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_smul_eq_nsmul ℤ]; exact ModularCurve.TateModule.pow_smul_apply hx n
  · rw [Nat.cast_smul_eq_nsmul ℤ]; exact hx.2 n

omit [Fact p.Prime] in
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
  rfl

theorem β_galois {G : Type} [Monoid G] [DistribMulAction G J] (σ : G)
    (x : ModularCurve.TateModule p J) :
    (((β hsmul).symm (_root_.TateModule.rep p J G σ (β hsmul x)) : ModularCurve.TateModule p J) :
        ℕ → J) = σ • (x : ℕ → J) :=
  rfl

end Bridge

section Main

attribute [local instance] ModularCurve.heckeModuleBar

set_option maxHeartbeats 3200000 in

theorem rational_comm (M lam : ℕ) [NeZero M] [Fact lam.Prime]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : ModularCurve.rationalHeckeAlgebra lam (ModularCurve.JZero M)) :
    (x : Module.End ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JZero M))) *
        ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ =
      ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ *
        x := by
  have hcomm := ModularCurve.heckeOperatorsCommuteBar M
  have hgen : ∀ t : ModularCurve.HeckeAlg,
      ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M) t *
          ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ =
        ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ *
          ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M) t := by
    intro t
    rw [ModularCurve.rationalHeckeRep_apply, ModularCurve.rationalGaloisRep_apply, ← LinearMap.baseChange_mul,
      ← LinearMap.baseChange_mul]
    congr 1
    apply LinearMap.ext
    intro y
    exact (ModularCurve.rep_tateModule_jZero_comm M lam hcomm σ t y).symm
  have hle : ModularCurve.rationalHeckeAlgebra lam (ModularCurve.JZero M) ≤ Subalgebra.centralizer ℚ_[lam]
      ({ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ} :
        Set (Module.End ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JZero M)))) := by
    show Algebra.adjoin ℚ_[lam] (Set.range (ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M))) ≤ _
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact (hgen t).symm
  have hx := hle x.2
  rw [Subalgebra.mem_centralizer_iff] at hx
  exact (hx _ rfl).symm

set_option maxHeartbeats 3200000 in

theorem rational_quadratic (M lam : ℕ) [NeZero M] [Fact lam.Prime]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓMlam : ¬ ℓ ∣ M * lam)
    (Apl : ValuationSubring (AlgebraicClosure ℚ)) (hApl : Apl.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : Apl.IsFrobeniusAt σ ℓ)
    (v : ModularCurve.RationalTateModule lam (ModularCurve.JZero M)) :
    ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v)
      - ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)
        (ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ v)
      + (ℓ : ℚ_[lam]) • v = 0 := by
  have hcomm := ModularCurve.heckeOperatorsCommuteBar M
  have hQT : ∀ x : _root_.TateModule lam (ModularCurve.JZero M),
      _root_.TateModule.rep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
          (_root_.TateModule.rep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
        - (ModularCurve.tateHeckeRep lam (ModularCurve.JZero M) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) :
            Module.End ℤ_[lam] (_root_.TateModule lam (ModularCurve.JZero M)))
          (_root_.TateModule.rep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
        + (ℓ : ℤ_[lam]) • x = 0 := by
    intro x
    have e : ((ℓ : ℤ_[lam]) • x : _root_.TateModule lam (ModularCurve.JZero M)) = ℓ • x :=
      Nat.cast_smul_eq_nsmul ℤ_[lam] ℓ x
    rw [e]
    exact ModularCurve.frobeniusQuadratic_tateModule_jZero M lam hcomm hℓ hℓMlam Apl hApl σ hσ x
  have h := quad_baseChange (X := _root_.TateModule lam (ModularCurve.JZero M)) ℚ_[lam]
    (_root_.TateModule.rep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ)
    (ModularCurve.tateHeckeRep lam (ModularCurve.JZero M) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)) (ℓ : ℤ_[lam]) (ℓ : ℚ_[lam])
    (map_natCast _ ℓ) hQT v
  rw [ModularCurve.rationalGaloisRep_apply, ModularCurve.rationalHeckeRep_apply]
  exact h

abbrev GoodPrime (M : ℕ) (S : Finset ℕ) : Type := {q : ℕ // q.Prime ∧ ¬ q ∣ M ∧ q ∉ (↑S : Set ℕ)}

def goodOp (M lam : ℕ) [NeZero M] [Fact lam.Prime] (S : Finset ℕ) (q : GoodPrime M S) :
    ModularCurve.rationalHeckeAlgebra lam (ModularCurve.JZero M) :=
  ⟨ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M) (ModularCurve.heckeGen ⟨q.1, q.2.1⟩),
    ModularCurve.rationalHeckeRep_mem_rationalHeckeAlgebra lam _ _⟩

set_option maxHeartbeats 3200000 in

theorem exists_transport_ops (M lam : ℕ) [NeZero M] [Fact lam.Prime]
    (O'' : Type) [CommRing O''] [Algebra ℤ_[lam] O'']
    (K : Type) [Field K] [Algebra O'' K] [Algebra ℤ_[lam] K] [IsScalarTower ℤ_[lam] O'' K]
    [Algebra ℚ_[lam] K] [IsScalarTower ℤ_[lam] ℚ_[lam] K]
    [Module ℤ_[lam] (ModularCurve.TateModule lam (ModularCurve.JZero M))]
    (hsmul : ∀ (a : ℤ_[lam]) (x : ModularCurve.TateModule lam (ModularCurve.JZero M)) (n : ℕ),
      ((a • x : ModularCurve.TateModule lam (ModularCurve.JZero M)) : ℕ → ModularCurve.JZero M) n =
        (PadicInt.toZModPow n a).val • (x : ℕ → ModularCurve.JZero M) n)
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M)))
    (hρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x y : ModularCurve.TateModule lam (ModularCurve.JZero M)),
      (y : ℕ → ModularCurve.JZero M) = σ • (x : ℕ → ModularCurve.JZero M) →
        ∀ a : O'', ρM σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] y)
    (TM : ModularCurve.HeckeAlg →+*
      Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M)))
    (hT : ∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : ModularCurve.TateModule lam (ModularCurve.JZero M)),
      TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x)) :
    ∃ Θ : (K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M))) ≃ₗ[K]
        K ⊗[ℚ_[lam]] ModularCurve.RationalTateModule lam (ModularCurve.JZero M),
      (∀ (t : ModularCurve.HeckeAlg) v, Θ ((TM t).baseChange K v) =
        ((ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M) t).baseChange K) (Θ v)) ∧
      (∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) v, Θ ((ρM τ).baseChange K v) =
        ((ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M)
          (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ).baseChange K) (Θ v)) := by
  have htr := exists_transport₂ (T := ModularCurve.TateModule lam (ModularCurve.JZero M))
    (T' := _root_.TateModule lam (ModularCurve.JZero M)) O'' K (β hsmul)
  obtain ⟨Θ, hΘ⟩ := htr
  refine ⟨Θ, fun t v => ?_, fun τ v => ?_⟩
  · rw [ModularCurve.rationalHeckeRep_apply]
    exact hΘ (TM t) (ModularCurve.tateHeckeRep lam (ModularCurve.JZero M) t) (fun a x => by
      rw [hT, ← β_hecke hsmul, LinearEquiv.symm_apply_apply]) v
  · rw [ModularCurve.rationalGaloisRep_apply]
    exact hΘ (ρM τ) (_root_.TateModule.rep lam (ModularCurve.JZero M)
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ) (fun a x =>
        hρ τ x _ (β_galois hsmul τ x) a) v

set_option maxHeartbeats 3200000 in

theorem map_eq_EV (M lam : ℕ) [NeZero M] [Fact lam.Prime] (S : Finset ℕ)
    (K : Type) [Field K] [Algebra ℚ_[lam] K] {L : Type} [AddCommGroup L] [Module K L]
    (Θ : L ≃ₗ[K] K ⊗[ℚ_[lam]] ModularCurve.RationalTateModule lam (ModularCurve.JZero M))
    (TK : ModularCurve.HeckeAlg → Module.End K L)
    (hΘT : ∀ (t : ModularCurve.HeckeAlg) v, Θ (TK t v) =
      ((ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M) t).baseChange K) (Θ v))
    (aK : GoodPrime M S → K) (W : Submodule K L)
    (hWmem : ∀ v, v ∈ W ↔ ∀ q : GoodPrime M S, TK (ModularCurve.heckeGen ⟨q.1, q.2.1⟩) v = aK q • v) :
    W.map (Θ : L →ₗ[K] _) =
      EV (ModularCurve.rationalHeckeAlgebra lam (ModularCurve.JZero M)) K (goodOp M lam S) aK := by
  apply Submodule.ext
  intro v
  constructor
  · intro hv
    have hv' := Submodule.mem_map.mp hv
    obtain ⟨w, hw, hwv⟩ := hv'
    subst hwv
    rw [mem_EV_iff]
    intro q
    show ((ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M)
      (ModularCurve.heckeGen ⟨q.1, q.2.1⟩)).baseChange K) (Θ w) = aK q • Θ w
    rw [← hΘT, (hWmem w).mp hw q, map_smul]
  · intro hv
    refine Submodule.mem_map.mpr ⟨Θ.symm v, ?_, Θ.apply_symm_apply v⟩
    rw [hWmem]
    intro q
    apply Θ.injective
    rw [hΘT, map_smul, Θ.apply_symm_apply]
    exact (mem_EV_iff _ K (goodOp M lam S) aK v).mp hv q

end Main

end OrdPtFrobTrace
p2m_reactivate "P2MW.S_CuspForm_IsNewform_frobeniusTrace_of_eigenPlane_tateModule_jZero.OrdPtFrobTrace"

set_option maxHeartbeats 6400000 in
open OrdPtFrobTrace in

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
    ∀ [Module ℤ_[lam] (ModularCurve.TateModule lam (JZero M))]
      (_hsmul : ∀ (a : ℤ_[lam]) (x : ModularCurve.TateModule lam (JZero M)) (n : ℕ),
        ((a • x : ModularCurve.TateModule lam (JZero M)) : ℕ → JZero M) n =
          (PadicInt.toZModPow n a).val • (x : ℕ → JZero M) n)
      (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
        Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M)))
      (_hρ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x y : ModularCurve.TateModule lam (JZero M)),
        (y : ℕ → JZero M) = σ • (x : ℕ → JZero M) →
          ∀ a : O'', ρM σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] y)
      (TM : ModularCurve.HeckeAlg →+* Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M)))
      (_hT : ∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : ModularCurve.TateModule lam (JZero M)),
        TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x))
      (W : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M))))
      (_hW2 : Module.finrank K W = 2)
      (_hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
        (ρM σ).baseChange K w ∈ W)
      (_hWT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))), ∀ w ∈ W,
        (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
          φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • w),
    ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))), ℓ ≠ lam →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace K W (((ρM σ).baseChange K).restrict (_hW σ)) =
            φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := by
  letI := ModularCurve.heckeModuleBar M
  intro inst hsmul ρM hρ TM hT W hW2 hW hWT ℓ hℓ hℓN hℓS hℓlam Apl hApl σ hσ

  letI algZpK : Algebra ℤ_[lam] K := ((algebraMap O'' K).comp (algebraMap ℤ_[lam] O'')).toAlgebra
  haveI towZ : IsScalarTower ℤ_[lam] O'' K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj : Function.Injective (algebraMap ℤ_[lam] K) := padicInt_ringHom_injective _
  letI algQpK : Algebra ℚ_[lam] K := (IsFractionRing.lift hinj : ℚ_[lam] →+* K).toAlgebra
  haveI towQ : IsScalarTower ℤ_[lam] ℚ_[lam] K :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsFractionRing.lift_algebraMap hinj x).symm)
  have hcomm := ModularCurve.heckeOperatorsCommuteBar M

  have hcmp :=
    ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jZero_padicInt_tensor_periodLattice
      M lam (ModularCurve.heckeInputsAll M) hcomm (ModularCurve.periodLatticeHeckeStable M)
  obtain ⟨eΛ, -⟩ := hcmp
  have hbas := ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top M
  obtain ⟨nΛ, bΛ, -, -⟩ := hbas
  haveI : Module.Finite ℤ_[lam] (ℤ_[lam] ⊗[ℤ] ModularCurve.periodLattice M) :=
    Module.Finite.of_basis (bΛ.baseChange ℤ_[lam])
  haveI : Module.Finite ℤ_[lam] (_root_.TateModule lam (ModularCurve.JZero M)) :=
    Module.Finite.equiv eΛ.symm
  haveI : Module.Finite K (K ⊗[ℚ_[lam]] ModularCurve.RationalTateModule lam (ModularCurve.JZero M)) :=
    inferInstance

  have htr := exists_transport_ops M lam O'' K hsmul ρM hρ TM hT
  obtain ⟨Θ, hΘT, hΘG⟩ := htr
  haveI : Module.Finite K (K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M))) :=
    Module.Finite.equiv Θ.symm

  have hmult :=
    hg.exists_heckeEigenspace_tateModule_jZero_finrank_eq_two lam S chig hchig O'' K φ hsmul TM hT
  obtain ⟨E₀, hE₀2, hE₀mem⟩ := hmult
  have hWE₀ : W = E₀ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · intro w hw
      exact (hE₀mem w).mpr (fun ℓ' hℓ' hℓ'N hℓ'S => hWT ℓ' hℓ' hℓ'N hℓ'S w hw)
    · rw [hW2, hE₀2]
  have hWmem : ∀ v, v ∈ W ↔ ∀ q : GoodPrime M S,
      (TM (ModularCurve.heckeGen ⟨q.1, q.2.1⟩)).baseChange K v =
        φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T q.2.1 q.2.2.1 q.2.2.2)) • v := fun v => by
    rw [hWE₀, hE₀mem]
    exact ⟨fun h q => h q.1 q.2.1 q.2.2.1 q.2.2.2, fun h ℓ' hℓ' hℓ'N hℓ'S => h ⟨ℓ', hℓ', hℓ'N, hℓ'S⟩⟩

  have hRT := ModularCurve.rationalRankTwoCyclotomic_family M lam (Nat.pos_of_ne_zero (NeZero.ne M)) Fact.out
  unfold ModularCurve.RationalRankTwoCyclotomic ModularCurve.RationalRankTwoCyclotomicOf at hRT
  obtain ⟨bA, hbA⟩ := hRT
  let Ar := ModularCurve.rationalHeckeAlgebra lam (ModularCurve.JZero M)
  have hσA : ∀ x : Ar, (x : Module.End ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JZero M))) *
      (ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ)
      = (ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ) * x :=
    fun x => rational_comm M lam σ x
  let c : Fin 2 → Fin 2 → Ar := fun j i => bA.repr ((ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ) (bA j)) i
  have hc : ∀ j : Fin 2, (ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ) (bA j) =
      (c j 0 : Module.End ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JZero M))) (bA 0) +
      (c j 1 : Module.End ℚ_[lam] (ModularCurve.RationalTateModule lam (ModularCurve.JZero M))) (bA 1) := by
    intro j
    conv_lhs => rw [← bA.sum_repr ((ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ) (bA j))]
    rw [Fin.sum_univ_two]
    rfl
  have hℓMlam : ¬ ℓ ∣ M * lam := by
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).mp h with h1 | h2
    · exact hℓN h1
    · exact hℓlam ((Nat.prime_dvd_prime_iff_eq hℓ Fact.out).mp h2)
  have hdetA : c 0 0 * c 1 1 - c 1 0 * c 0 1 = algebraMap ℚ_[lam] Ar (ℓ : ℚ_[lam]) :=
    (hbA ℓ hℓ hℓMlam Apl hApl σ hσ).trans (map_natCast (algebraMap ℚ_[lam] Ar) ℓ).symm

  let tA : GoodPrime M S → Ar := goodOp M lam S
  let aK : GoodPrime M S → K := fun q => φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T q.2.1 q.2.2.1 q.2.2.2))
  have hEV : W.map (Θ : _ →ₗ[K] _) = EV Ar K tA aK :=
    map_eq_EV M lam S K Θ (fun t => (TM t).baseChange K) hΘT aK W hWmem

  let jW : W →ₗ[K] K ⊗[ℚ_[lam]] ModularCurve.RationalTateModule lam (ModularCurve.JZero M) :=
    (Θ : _ →ₗ[K] _) ∘ₗ W.subtype
  have hj : Function.Injective jW := Θ.injective.comp W.injective_subtype
  have hjE : ∀ w : W, jW w ∈ EV Ar K tA aK := fun w =>
    hEV.le (Submodule.mem_map.mpr ⟨w, w.2, rfl⟩)
  have hEj : ∀ v ∈ EV Ar K tA aK, ∃ w : W, jW w = v := fun v hv => by
    obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.mp (hEV.ge hv)
    exact ⟨⟨y, hy⟩, hyv⟩
  have hFE : ∀ w : W, jW ((((ρM σ).baseChange K).restrict (hW σ)) w) =
      ((ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K)
        (jW w) := fun w => by
    show Θ (((((ρM σ).baseChange K).restrict (hW σ)) w : W) : _) = _
    rw [LinearMap.coe_restrict_apply]
    exact hΘG σ _
  have hdetW := det_eq_of_plane Ar bA K tA aK W jW hj hjE hEj hW2
    (ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ)
    hσA c hc (ℓ : ℚ_[lam]) hdetA (((ρM σ).baseChange K).restrict (hW σ)) hFE

  have hQK : ∀ v : K ⊗[ℚ_[lam]] ModularCurve.RationalTateModule lam (ModularCurve.JZero M),
      ((ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K)
        (((ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K) v)
      - ((ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K)
        (((ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange K) v)
      + (ℓ : K) • v = 0 := by
    intro v
    exact quad_baseChange (X := ModularCurve.RationalTateModule lam (ModularCurve.JZero M)) K
      (ModularCurve.rationalGaloisRep lam (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ)
      (ModularCurve.rationalHeckeRep lam (ModularCurve.JZero M) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)) (ℓ : ℚ_[lam]) (ℓ : K)
      (map_natCast (algebraMap ℚ_[lam] K) ℓ) (rational_quadratic M lam hℓ hℓMlam Apl hApl σ hσ) v
  have hQL : ∀ v : K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M)),
      ((ρM σ).baseChange K) (((ρM σ).baseChange K) v)
        - ((TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K) (((ρM σ).baseChange K) v) + (ℓ : K) • v = 0 :=
    quad_of_transport Θ ((ρM σ).baseChange K) ((TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K) _ _
      (hΘG σ) (hΘT (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)) (ℓ : K) hQK
  have hquadW := restrict_quadratic
    (X := K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (ModularCurve.JZero M)))
    ((ρM σ).baseChange K) ((TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K)
    (φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) (ℓ : K) W (hW σ) hQL
    (fun v hv => hWT ℓ hℓ hℓN hℓS _ (hW σ v hv))

  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  exact trace_eq_of_quadratic_of_det' W hW2 (((ρM σ).baseChange K).restrict (hW σ))
    (φ (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))) (ℓ : K) hquadW
    (hdetW.trans (map_natCast (algebraMap ℚ_[lam] K) ℓ)) hℓK

end
p2m_reactivate "P2MW.S_CuspForm_IsNewform_frobeniusTrace_of_eigenPlane_tateModule_jZero.OrdPtFrobTrace"

end S_CuspForm_IsNewform_frobeniusTrace_of_eigenPlane_tateModule_jZero
end P2MW
export P2MW.S_CuspForm_IsNewform_frobeniusTrace_of_eigenPlane_tateModule_jZero (solution)

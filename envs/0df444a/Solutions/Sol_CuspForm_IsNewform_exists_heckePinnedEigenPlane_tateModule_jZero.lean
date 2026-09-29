-- Prove2me | solution 1 for CuspForm.IsNewform.exists_heckePinnedEigenPlane_tateModule_jZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4133ff9e-8977-5d2b-9a54-60b2e3d8c5ea

import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_CuspForm_IsNewform_exists_heckeEigenspace_tateModule_jZero_finrank_eq_two
import Theorems.Thm_CuspForm_IsNewform_frobeniusTrace_of_eigenPlane_tateModule_jZero
import Theorems.Thm_CuspForm_IsNewform_heckeU_smul_of_mem_heckeEigenspace_tateModule_jZero
import Theorems.Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.AdicCompletion.RingHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_exists_heckePinnedEigenPlane_tateModule_jZero
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one"
p2m_attr_erase "simp" "ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.coe_traceLin_apply"
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
open ModularCurve TensorProduct
set_option synthInstance.maxHeartbeats 1600000

namespace OrdPtProducer

section AlgZp

variable (lam : ℕ) [Fact lam.Prime] (O' : Type) [CommRing O'] [IsLocalRing O']
  [IsAdicComplete (IsLocalRing.maximalIdeal O') O']

omit [Fact lam.Prime] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] in

theorem natCast_pow_eq_zero (hlam : (lam : O') ∈ IsLocalRing.maximalIdeal O') (n : ℕ) :
    ((lam ^ n : ℕ) : O' ⧸ IsLocalRing.maximalIdeal O' ^ n) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O' ^ n)),
    Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.pow_mem_pow hlam n

noncomputable def levelHom (hlam : (lam : O') ∈ IsLocalRing.maximalIdeal O') (n : ℕ) :
    ℤ_[lam] →+* O' ⧸ IsLocalRing.maximalIdeal O' ^ n :=
  (ZMod.castHom (ringChar.dvd (natCast_pow_eq_zero lam O' hlam n))
      (O' ⧸ IsLocalRing.maximalIdeal O' ^ n)).comp (PadicInt.toZModPow n)

omit [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] in
theorem levelHom_compat (hlam : (lam : O') ∈ IsLocalRing.maximalIdeal O') {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O') hle).comp (levelHom lam O' hlam n) =
      levelHom lam O' hlam m := by
  unfold levelHom
  rw [← RingHom.comp_assoc, ← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

noncomputable def padicHom (hlam : (lam : O') ∈ IsLocalRing.maximalIdeal O') : ℤ_[lam] →+* O' :=
  IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal O') (levelHom lam O' hlam)
    (fun hle => levelHom_compat lam O' hlam hle)

end AlgZp

section Generic

variable {A : Type} [CommRing A] {N : Type} [AddCommGroup N] [Module A N]
  (K : Type) [Field K] [Algebra A K]

theorem baseChange_comm (f g : Module.End A N) (h : f ∘ₗ g = g ∘ₗ f) (v : K ⊗[A] N) :
    f.baseChange K (g.baseChange K v) = g.baseChange K (f.baseChange K v) := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h, LinearMap.baseChange_comp,
    LinearMap.comp_apply]

end Generic

section Comm

variable {G : Type} [Group G] {J : Type} [AddCommGroup J] [Module ModularCurve.HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G ModularCurve.HeckeAlg J]
  (lam : ℕ) [Fact lam.Prime] (O'' : Type) [CommRing O''] [Algebra ℤ_[lam] O'']
  [Module ℤ_[lam] (ModularCurve.TateModule lam J)]

theorem rho_TM_comm
    (ρM : G →* Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam J))
    (hρ : ∀ (σ : G) (x y : ModularCurve.TateModule lam J), (y : ℕ → J) = σ • (x : ℕ → J) →
      ∀ a : O'', ρM σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] y)
    (TM : ModularCurve.HeckeAlg →+* Module.End O'' (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam J))
    (hT : ∀ (t : ModularCurve.HeckeAlg) (a : O'') (x : ModularCurve.TateModule lam J),
      TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x))
    (σ : G) (t : ModularCurve.HeckeAlg) :
    (TM t) ∘ₗ (ρM σ) = (ρM σ) ∘ₗ (TM t) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x

  let y : ModularCurve.TateModule lam J := ⟨σ • (x : ℕ → J), ModularCurve.TateModule.smul_mem σ x.2⟩
  let y' : ModularCurve.TateModule lam J := ⟨σ • ((t • x : ModularCurve.TateModule lam J) : ℕ → J), ModularCurve.TateModule.smul_mem σ (t • x).2⟩
  have hty : t • y = y' := by
    apply Subtype.ext
    funext n
    change t • (σ • (x : ℕ → J) n) = σ • ((t • x : ModularCurve.TateModule lam J) : ℕ → J) n
    rw [Submodule.coe_smul, Pi.smul_apply]
    exact (smul_comm σ t ((x : ℕ → J) n)).symm
  have e1 : ρM σ (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] y := hρ σ x y rfl a
  have e2 : TM t (a ⊗ₜ[ℤ_[lam]] y) = a ⊗ₜ[ℤ_[lam]] (t • y) := hT t a y
  have e3 : TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x) := hT t a x
  have e4 : ρM σ (a ⊗ₜ[ℤ_[lam]] (t • x)) = a ⊗ₜ[ℤ_[lam]] y' := hρ σ (t • x) y' rfl a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3, e4, hty]

end Comm

section Transport

variable {M : ℕ} [NeZero M] (lam : ℕ) (S : Finset ℕ)

theorem coe_erase_subset : ((↑S : Set ℕ) \ {lam}) ⊆ (↑(S.erase lam) : Set ℕ) := by
  rw [Finset.coe_erase]

theorem heckeAlgebra_erase_le :
    CuspForm.heckeAlgebra M 2 (↑(S.erase lam) : Set ℕ) ≤ CuspForm.heckeAlgebra M 2 ((↑S : Set ℕ) \ {lam}) :=
  CuspForm.heckeAlgebra_mono (coe_erase_subset lam S)

end Transport

end OrdPtProducer

set_option maxHeartbeats 6400000 in
open OrdPtProducer in

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (lam : ℕ) [Fact lam.Prime]
    (S : Finset ℕ)
    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [Finite (IsLocalRing.ResidueField O')]
    [CharZero O'] (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (chig : CuspForm.heckeAlgebra M 2 ((↑S : Set ℕ) \ {lam}) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {lam})),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (iota : chig.range →+* O')
    (hlamS : lam ∈ S) (hMS : ∀ q : ℕ, q.Prime → q ∣ M → q ∈ S) :
    ∃ (O'' : Type) (_ : CommRing O'') (_ : IsDomain O'') (_ : IsDiscreteValuationRing O'')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O'') O'')
      (_ : Finite (IsLocalRing.ResidueField O'')) (_ : CharZero O'')
      (_ : Algebra O' O'') (_ : Module.Finite O' O'') (_ : IsLocalHom (algebraMap O' O''))
      (_ : Algebra ℤ_[lam] O''),
    Function.Injective (algebraMap O' O'') ∧
    ∀ (K : Type) [Field K] [Algebra O'' K] [IsFractionRing O'' K],
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
        TM t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] (t • x)),
    ∃ W : Submodule K (K ⊗[O''] (O'' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M))),
      Module.finrank K W = 2 ∧
      ∃ hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ W,
          (ρM σ).baseChange K w ∈ W,
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))), ∀ w ∈ W,
          (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
            algebraMap O'' K (algebraMap O' O''
              ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓN
                (fun h => hℓS (Set.mem_of_mem_diff h))))) • w) ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ ((S : Set ℕ))),
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.trace K W (((ρM σ).baseChange K).restrict (hW σ)) =
                algebraMap O'' K (algebraMap O' O''
                  ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓN
                (fun h => hℓS (Set.mem_of_mem_diff h)))))) ∧
        (∀ (hlamM : ¬ lam ∣ M), ∀ w ∈ W,
          (TM (ModularCurve.heckeGen ⟨lam, Fact.out⟩)).baseChange K w =
            algebraMap O'' K (algebraMap O' O''
              ((iota.comp chig.rangeRestrict)
                (CuspForm.heckeAlgebra.T (Fact.out : lam.Prime) hlamM (by simp)))) • w) ∧
        (∀ (hlamM : lam ∣ M), ∀ w ∈ W,
          (TM (ModularCurve.heckeGen ⟨lam, Fact.out⟩)).baseChange K w =
            algebraMap O'' K (algebraMap O' O''
              ((iota.comp chig.rangeRestrict)
                (CuspForm.heckeAlgebra.U (Fact.out : lam.Prime) hlamM (by simp)))) • w) := by
  have _ := hMS
  letI algZp : Algebra ℤ_[lam] O' := (padicHom lam O' hlamO').toAlgebra
  refine ⟨O', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.id O', inferInstance, inferInstance, algZp, fun _ _ h => by simpa using h, ?_⟩
  intro K _ _ _
  letI := ModularCurve.heckeModuleBar M
  intro _ hsmul ρM hρ TM hT
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O' K)

  have hlamS' : lam ∉ (↑(S.erase lam) : Set ℕ) := by simp
  let incl : CuspForm.heckeAlgebra M 2 (↑(S.erase lam) : Set ℕ) →ₐ[ℤ]
      CuspForm.heckeAlgebra M 2 ((↑S : Set ℕ) \ {lam}) :=
    Subalgebra.inclusion (heckeAlgebra_erase_le lam S)
  let chig' : CuspForm.heckeAlgebra M 2 (↑(S.erase lam) : Set ℕ) →+* ℂ := chig.comp incl.toRingHom
  have hout : ∀ {ℓ : ℕ}, ℓ ∉ (↑(S.erase lam) : Set ℕ) → ℓ ∉ ((↑S : Set ℕ) \ {lam}) := by
    intro ℓ hℓS' h
    rcases eq_or_ne ℓ lam with hℓlam | hℓlam
    · exact h.2 (by simp [hℓlam])
    · exact hℓS' (by simpa [hℓlam] using h.1)
  have hT_incl : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS' : ℓ ∉ (↑(S.erase lam) : Set ℕ))
      (h : ℓ ∉ ((↑S : Set ℕ) \ {lam})),
      incl (CuspForm.heckeAlgebra.T hℓ hℓM hℓS') = CuspForm.heckeAlgebra.T hℓ hℓM h :=
    fun ℓ hℓ hℓM hℓS' h => Subtype.ext rfl
  have hchig' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑(S.erase lam) : Set ℕ)),
      chig' (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ := by
    intro ℓ hℓ hℓM hℓS'
    change chig (incl (CuspForm.heckeAlgebra.T hℓ hℓM hℓS')) = _
    rw [hT_incl ℓ hℓ hℓM hℓS' (hout hℓS')]
    exact hchig ℓ hℓ hℓM (hout hℓS')
  have hle : chig'.range ≤ chig.range := by
    rintro _ ⟨t, rfl⟩
    exact ⟨incl t, rfl⟩
  let φ' : chig'.range →+* K := (algebraMap O' K).comp (iota.comp (Subring.inclusion hle))

  have hval : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS' : ℓ ∉ (↑(S.erase lam) : Set ℕ))
      (h : ℓ ∉ ((↑S : Set ℕ) \ {lam})),
      φ' (chig'.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓM hℓS')) =
        algebraMap O' K (algebraMap O' O'
          ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM h))) := by
    intro ℓ hℓ hℓM hℓS' h
    change algebraMap O' K (iota (Subring.inclusion hle (chig'.rangeRestrict _))) = _
    rw [Algebra.algebraMap_self_apply, RingHom.comp_apply]
    congr 2
  have hvalU : ∀ (hlamM : lam ∣ M),
      φ' (chig'.rangeRestrict (CuspForm.heckeAlgebra.U (Fact.out : lam.Prime) hlamM hlamS')) =
        algebraMap O' K (algebraMap O' O'
          ((iota.comp chig.rangeRestrict)
            (CuspForm.heckeAlgebra.U (Fact.out : lam.Prime) hlamM (by simp)))) := by
    intro hlamM
    change algebraMap O' K (iota (Subring.inclusion hle (chig'.rangeRestrict _))) = _
    rw [Algebra.algebraMap_self_apply, RingHom.comp_apply]
    congr 2

  have hmult := hg.exists_heckeEigenspace_tateModule_jZero_finrank_eq_two lam (S.erase lam) chig' hchig' O'
    K φ' hsmul TM hT
  obtain ⟨E, hE2, hEmem⟩ := hmult

  have hcomm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : ModularCurve.HeckeAlg)
      (v : K ⊗[O'] (O' ⊗[ℤ_[lam]] ModularCurve.TateModule lam (JZero M))),
      (TM t).baseChange K ((ρM σ).baseChange K v) = (ρM σ).baseChange K ((TM t).baseChange K v) := by
    haveI : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg (JZero M) :=
      ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar M (ModularCurve.heckeOperatorsCommuteBar M)
    exact fun σ t v => baseChange_comm K (TM t) (ρM σ) (rho_TM_comm lam O' ρM hρ TM hT σ t) v
  have hW : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ w ∈ E, (ρM σ).baseChange K w ∈ E := by
    intro σ w hw
    rw [hEmem]
    intro ℓ hℓ hℓN hℓS'
    rw [hcomm, (hEmem w).mp hw ℓ hℓ hℓN hℓS', map_smul]

  have hsub : ∀ {ℓ : ℕ}, ℓ ∉ (↑S : Set ℕ) → ℓ ∉ (↑(S.erase lam) : Set ℕ) := by
    intro ℓ h h'
    exact h (Finset.mem_coe.mpr (Finset.mem_erase.mp (Finset.mem_coe.mp h')).2)
  have hET : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑(S.erase lam) : Set ℕ)), ∀ w ∈ E,
      (TM (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)).baseChange K w =
        φ' (chig'.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • w :=
    fun ℓ hℓ hℓN hℓS w hw => (hEmem w).mp hw ℓ hℓ hℓN hℓS
  refine ⟨E, hE2, hW, ?_, ?_, ?_, ?_⟩
  · intro ℓ hℓ hℓN hℓS w hw
    rw [hET ℓ hℓ hℓN (hsub hℓS) w hw, hval ℓ hℓ hℓN (hsub hℓS) (fun h => hℓS (Set.mem_of_mem_diff h))]
  · intro ℓ hℓ hℓN hℓS A hA σ hσ
    have hℓlam : ℓ ≠ lam := fun h => hℓS (h ▸ Finset.mem_coe.mpr hlamS)
    rw [hg.frobeniusTrace_of_eigenPlane_tateModule_jZero lam (S.erase lam) chig' hchig' O' K φ' hsmul ρM hρ
      TM hT E hE2 hW hET ℓ hℓ hℓN (hsub hℓS) hℓlam A hA σ hσ,
      hval ℓ hℓ hℓN (hsub hℓS) (fun h => hℓS (Set.mem_of_mem_diff h))]
  · intro hlamM w hw
    rw [hET lam Fact.out hlamM hlamS' w hw, hval lam Fact.out hlamM hlamS' (by simp)]
  · intro hlamM w hw
    rw [CuspForm.IsNewform.heckeU_smul_of_mem_heckeEigenspace_tateModule_jZero hg lam (S.erase lam) hlamS'
      hlamM chig' hchig' O' K φ' hsmul TM hT w ((hEmem w).mp hw), hvalU hlamM]

end S_CuspForm_IsNewform_exists_heckePinnedEigenPlane_tateModule_jZero
end P2MW
export P2MW.S_CuspForm_IsNewform_exists_heckePinnedEigenPlane_tateModule_jZero (solution)

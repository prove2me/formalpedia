-- Prove2me | solution 1 for CuspForm.exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/18426f28-d0df-57d3-8ad8-7a5ebd7238d8

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_Eisenstein
import Theorems.Thm_CuspForm_exists_qIntegral_eisenstein_eigen_mod_of_injective
import Theorems.Thm_ModularCurve_dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod
import Theorems.Thm_CuspForm_hasIntegralBasis_iff_hasIntegralStructure_two
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_ModularCurve_addOrderOf_cuspidalClass_eq_eisensteinNumerator
import Theorems.Thm_ModularCurve_sharpUnitInvariant
import Theorems.Thm_ModularCurve_sharpUnitNecessary
import Theorems.Thm_ModularCurve_exists_ringHom_heckeAlgebra_heckeOperatorBar
import Theorems.Thm_ModularCurve_eisensteinIdeal_smul_cuspidalClass
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

open ModularCurve

namespace R3aux4

private def evalKer (p : ℕ) [NeZero p]
    (Φ : CuspForm.heckeAlgebra p 2 ∅ →+* Module.End ℤ (JZero p)) :
    Ideal (CuspForm.heckeAlgebra p 2 ∅) where
  carrier := {t | Φ t (cuspidalClass p) = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [Φ.map_add, LinearMap.add_apply, ha, hb, add_zero]
  zero_mem' := by
    show Φ 0 (cuspidalClass p) = 0
    rw [Φ.map_zero, LinearMap.zero_apply]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    rw [Φ.map_mul, Module.End.mul_apply, hx, (Φ r).map_zero]

theorem hinj_of_addOrderOf (p : ℕ) [Fact p.Prime]
    (horder : addOrderOf (cuspidalClass p) = eisensteinNumerator p) :
    ∀ c : ℤ,
      algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈
          Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔
            Ideal.span {(eisensteinNumerator p : CuspForm.heckeAlgebra p 2 ∅)} →
        (eisensteinNumerator p : ℤ) ∣ c := by
  obtain ⟨Φ, hT, hU⟩ := ModularCurve.exists_ringHom_heckeAlgebra_heckeOperatorBar p
  have h : HeckeOperatorsCommuteBar p := ModularCurve.heckeOperatorsCommuteBar p
  have hcomp : Φ.comp (heckeProj p) = heckeEvalBar h := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, heckeProj_C, heckeEvalBar_C,
        eq_intCast (algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅)) a, map_intCast Φ a]
    · intro ℓ
      show (Φ.comp (heckeProj p)) (heckeGen ℓ) = heckeEvalBar h (heckeGen ℓ)
      rw [RingHom.comp_apply, heckeEvalBar_heckeGen h ℓ]
      by_cases hdvd : (ℓ : ℕ) ∣ p
      · rw [heckeProj_heckeGen_of_dvd ℓ hdvd, hU ℓ hdvd (Set.notMem_empty _)]
      · rw [heckeProj_heckeGen_of_not_dvd ℓ hdvd, hT ℓ hdvd (Set.notMem_empty _)]
  have htor : eisensteinNumerator p • cuspidalClass p = 0 :=
    horder ▸ addOrderOf_nsmul_eq_zero (cuspidalClass p)
  have hmap : Ideal.map (heckeProj p) (eisensteinIdeal p) ≤ evalKer p Φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap]
    show Φ (heckeProj p i) (cuspidalClass p) = 0
    have h1 : Φ (heckeProj p i) = heckeEvalBar h i := by
      rw [← RingHom.comp_apply, hcomp]
    rw [h1, ← heckeModuleBar_smul_def h]
    exact ModularCurve.eisensteinIdeal_smul_cuspidalClass p i hi
  have hspan : Ideal.span {(eisensteinNumerator p : CuspForm.heckeAlgebra p 2 ∅)} ≤
      evalKer p Φ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    show Φ (eisensteinNumerator p : CuspForm.heckeAlgebra p 2 ∅) (cuspidalClass p) = 0
    rw [map_natCast Φ (eisensteinNumerator p), Module.End.natCast_apply]
    exact htor
  intro c hc
  have hker : Φ (algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c) (cuspidalClass p) = 0 :=
    sup_le hmap hspan hc
  have hzero : c • cuspidalClass p = 0 := by
    rwa [eq_intCast (algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅)) c, map_intCast Φ c,
      Module.End.intCast_apply] at hker
  have hdvd : ((addOrderOf (cuspidalClass p) : ℕ) : ℤ) ∣ c :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr hzero
  rwa [horder] at hdvd

end R3aux4

namespace R3N

theorem one_le_eisensteinNumerator (p : ℕ) (hp : p.Prime) :
    1 ≤ eisensteinNumerator p := by
  unfold eisensteinNumerator
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hgcdpos : 0 < Nat.gcd (p - 1) 12 := Nat.gcd_pos_of_pos_left _ hpos
  rw [Nat.one_le_div_iff hgcdpos]
  exact Nat.le_of_dvd hpos (Nat.gcd_dvd_left _ _)

theorem qCoeff_coe_zero (N n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2)) n = 0 := by
  rw [ModularFormClass.qCoeff, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero]
  exact map_zero (PowerSeries.coeff n)

theorem zero_mem_qIntegralSet (N : ℕ) :
    (0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) ∈ CuspForm.qIntegralSet N := by
  intro n
  rw [qCoeff_coe_zero]
  exact zero_mem _

theorem degenerate (p : ℕ) (h1 : eisensteinNumerator p = 1) :
    ∃ f ∈ CuspForm.qIntegralSet p, ∃ af : ℕ → ℤ,
      (∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
        IsCoprime (af 1) (eisensteinNumerator p : ℤ) ∧
          ∀ n : ℕ, n ≠ 0 →
            (eisensteinNumerator p : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1 := by
  refine ⟨0, zero_mem_qIntegralSet p, fun _ => 0, fun n => ?_, ?_, fun n _ => ?_⟩
  · rw [qCoeff_coe_zero, Int.cast_zero]
  · rw [h1, Nat.cast_one]
    exact isCoprime_one_right
  · rw [h1, Nat.cast_one]
    exact one_dvd _

theorem main (p : ℕ) [Fact p.Prime] (hn2 : 2 ≤ eisensteinNumerator p)
    (hWnec : SharpUnitNecessary p) :
    ∃ f ∈ CuspForm.qIntegralSet p, ∃ af : ℕ → ℤ,
      (∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
        IsCoprime (af 1) (eisensteinNumerator p : ℤ) ∧
          ∀ n : ℕ, n ≠ 0 →
            (eisensteinNumerator p : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1 := by
  have hIB : CuspForm.HasIntegralBasis p :=
    (CuspForm.hasIntegralBasis_iff_hasIntegralStructure_two p).mpr
      (CuspForm.hasIntegralStructure_two p)
  have horder : addOrderOf (cuspidalClass p) = eisensteinNumerator p :=
    addOrderOf_cuspidalClass_eq_eisensteinNumerator p (sharpUnitInvariant p) hWnec
  obtain ⟨f, hf, af, haf, h1, hT, hU⟩ :=
    CuspForm.exists_qIntegral_eisenstein_eigen_mod_of_injective p (eisensteinNumerator p) hn2 hIB
      (R3aux4.hinj_of_addOrderOf p horder)
  exact ⟨f, hf, af, haf, h1,
    dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod p (eisensteinNumerator p) af hT hU⟩

end R3N

theorem solution
    (p : ℕ) [Fact p.Prime] :
    ∃ f ∈ CuspForm.qIntegralSet p, ∃ af : ℕ → ℤ,
      (∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
        IsCoprime (af 1) (eisensteinNumerator p : ℤ) ∧
          ∀ n : ℕ, n ≠ 0 →
            (eisensteinNumerator p : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1 := by
  rcases Nat.lt_or_ge (eisensteinNumerator p) 2 with hn1 | hn2
  · exact R3N.degenerate p
      (le_antisymm (Nat.lt_succ_iff.mp hn1) (R3N.one_le_eisensteinNumerator p Fact.out))
  · exact R3N.main p hn2 (ModularCurve.sharpUnitNecessary p)

end S_CuspForm_exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator
end P2MW
export P2MW.S_CuspForm_exists_qIntegral_qCoeff_congr_sigmaPrimeTo_eisensteinNumerator (solution)

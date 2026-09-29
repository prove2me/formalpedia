-- Prove2me | solution 1 for CuspForm.genusFormula_le_finrank_gamma0_weight_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0ac98354-05c8-5929-8e62-aec697f33338

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Theorems.Thm_ModularCurve_exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar
import Theorems.Thm_ModularCurve_diffQExpBar_injective_of_neZero
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import Theorems.Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_genusFormula_le_finrank_gamma0_weight_two
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

open ModularCurve AlgebraicCurve

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

theorem linearIndependent_ringHom_comp_of_linearIndependent {K L : Type*} [Field K] [Field L]
    (ι : K →+* L) {n : ℕ} {X : Type*} {v : Fin n → X → K} (hv : LinearIndependent K v) :
    LinearIndependent L (fun i x => ι (v i x)) := by
  classical
  letI : Algebra K L := ι.toAlgebra
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc i
  let B := Module.Basis.ofVectorSpace K L
  have hrel : ∀ k, ∑ j, (B.repr (c j) k) • v j = 0 := by
    intro k
    funext x
    have hx := congr_fun hc x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx ⊢
    have hx' : ∑ j, (v j x) • c j = 0 := by
      rw [← hx]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    have h2 : B.repr (∑ j, (v j x) • c j) k = 0 := by
      rw [hx', map_zero, Finsupp.zero_apply]
    rw [map_sum, Finsupp.finset_sum_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have hzero : B.repr (c i) = 0 := by
    ext k
    rw [Finsupp.zero_apply]
    exact hv _ (hrel k) i
  exact (LinearEquiv.map_eq_zero_iff B.repr).mp hzero

set_option maxHeartbeats 6400000 in
theorem solution (N : ℕ) [NeZero N] :
    ModularCurve.genusFormula N ≤ (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℚ) := by
  classical
  haveI hCO := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI hEFT := ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI hCD := ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
  haveI hfinS := CuspForm.finiteDimensional_Gamma0 N 2
  obtain ⟨hfinΩ, hrank⟩ :=
    AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus
      (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))
  rw [← ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula N, ← hrank]
  haveI : Module.Finite (AlgebraicClosure ℚ) ↥(regularDifferentialsBar N) := hfinΩ

  suffices key : Module.finrank (AlgebraicClosure ℚ) ↥(regularDifferentialsBar N)
      ≤ Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) by
    first | exact Nat.cast_le.mpr key | exact_mod_cast key

  let b := Module.finBasis (AlgebraicClosure ℚ) ↥(regularDifferentialsBar N)

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ι₀ : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom

  have hex : ∀ i : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(regularDifferentialsBar N)),
      ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        ModularCurve.coeffMap ι₀
            (ModularCurve.diffQExpBar N (b i : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 f) := fun i =>
    ModularCurve.exists_cuspForm_coeffMap_diffQExpBar_eq_qExpansion_of_mem_regularDifferentialsBar
      N ι₀ (b i : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (b i).2
  choose f hf using hex

  let v : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(regularDifferentialsBar N)) → ℤ → AlgebraicClosure ℚ :=
    fun i n => (ModularCurve.diffQExpBar N (b i : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])).coeff n
  have hv_def : ∀ i n, v i n =
      (ModularCurve.diffQExpBar N (b i : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])).coeff n :=
    fun _ _ => rfl

  let Θ : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] →ₗ[AlgebraicClosure ℚ] LaurentSeries (AlgebraicClosure ℚ) :=
    (ModularCurve.diffQExpBar N).restrictScalars (AlgebraicClosure ℚ)
  have hΘ : ∀ ω, Θ ω = ModularCurve.diffQExpBar N ω := fun ω => rfl
  have hcoeff_sum : ∀ (s : Finset (Fin (Module.finrank (AlgebraicClosure ℚ) ↥(regularDifferentialsBar N))))
      (x : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(regularDifferentialsBar N)) → LaurentSeries (AlgebraicClosure ℚ))
      (n : ℤ), (∑ i ∈ s, x i).coeff n = ∑ i ∈ s, (x i).coeff n := by
    intro s x n
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HahnSeries.coeff_add, ih]

  have hv : LinearIndependent (AlgebraicClosure ℚ) v := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    have hsum : Θ ((∑ i, d i • b i : ↥(regularDifferentialsBar N)) : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) = 0 := by
      rw [Submodule.coe_sum, map_sum]
      ext n
      have hdn := congr_fun hd n
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hdn
      rw [hcoeff_sum, HahnSeries.coeff_zero, ← hdn]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, map_smul, HahnSeries.coeff_smul, smul_eq_mul]
      rw [hΘ, hv_def]
    rw [hΘ] at hsum
    have hzero : ((∑ i, d i • b i : ↥(regularDifferentialsBar N)) : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) = 0 :=
      ModularCurve.diffQExpBar_injective_of_neZero N (by rw [hsum, map_zero])
    have hzero' : (∑ i, d i • b i) = 0 := by
      first | exact (Submodule.coe_eq_zero).mp hzero | exact Subtype.ext hzero | exact_mod_cast hzero
    exact Fintype.linearIndependent_iff.mp b.linearIndependent d hzero'

  have hvC : LinearIndependent ℂ (fun i n => ι₀ (v i n)) :=
    linearIndependent_ringHom_comp_of_linearIndependent ι₀ hv

  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N

  have hcadd : ∀ φ ψ : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ⇑(φ + ψ) = ⇑φ + ⇑ψ := fun _ _ => rfl
  have hcsmul : ∀ (x : ℂ) (φ : CuspForm (CongruenceSubgroup.Gamma0 N) 2), ⇑(x • φ) = x • ⇑φ := fun _ _ => rfl
  have hczero : ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) = 0 := rfl

  have hqadd : ∀ φ ψ : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      UpperHalfPlane.qExpansion 1 (⇑φ + ⇑ψ) = UpperHalfPlane.qExpansion 1 ⇑φ + UpperHalfPlane.qExpansion 1 ⇑ψ := by
    intro φ ψ
    first
      | exact ModularFormClass.qExpansion_add one_pos hΓ φ ψ
      | exact ModularForm.qExpansion_add one_pos hΓ φ ψ
  have hqsmul : ∀ (x : ℂ) (φ : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      UpperHalfPlane.qExpansion 1 (x • ⇑φ) = x • UpperHalfPlane.qExpansion 1 ⇑φ := by
    intro x φ
    first
      | exact ModularFormClass.qExpansion_smul one_pos hΓ x φ
      | exact ModularForm.qExpansion_smul one_pos hΓ x φ
  have hqzero : UpperHalfPlane.qExpansion 1 (0 : UpperHalfPlane → ℂ) = 0 := by
    first
      | exact UpperHalfPlane.qExpansion_zero 1
      | simpa using hqsmul 0 0
  have hli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc

    have hqsum : ∀ s : Finset (Fin (Module.finrank (AlgebraicClosure ℚ) ↥(regularDifferentialsBar N))),
        UpperHalfPlane.qExpansion 1 ⇑(∑ i ∈ s, c i • f i) =
          ∑ i ∈ s, c i • UpperHalfPlane.qExpansion 1 ⇑(f i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.sum_empty, hczero, hqzero]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, hcadd, hqadd, hcsmul, hqsmul, ih]
    have hq : ∑ i, c i • UpperHalfPlane.qExpansion 1 ⇑(f i) = 0 := by
      rw [← hqsum Finset.univ, hc, hczero, hqzero]

    have hrel : ∑ i, c i • (fun n => ι₀ (v i n)) = 0 := by
      funext n
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hvi : ∀ i, ι₀ (v i n) =
          (HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(f i))).coeff n := by
        intro i
        rw [← hf i, ModularCurve.coeffMap_coeff]
      simp_rw [hvi]
      rcases n with m | m
      ·
        have h1 := congr_arg (PowerSeries.coeff m) hq
        rw [map_sum, map_zero] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul]
        first | rw [Int.ofNat_eq_natCast] | rw [Int.ofNat_eq_coe] | skip
        rw [HahnSeries.ofPowerSeries_apply_coeff]
      ·
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range, mul_zero]
        rintro ⟨k, hk⟩
        exact absurd hk (by simp)
    exact Fintype.linearIndependent_iff.mp hvC c hrel
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  exact hcard

end S_CuspForm_genusFormula_le_finrank_gamma0_weight_two
end P2MW
export P2MW.S_CuspForm_genusFormula_le_finrank_gamma0_weight_two (solution)

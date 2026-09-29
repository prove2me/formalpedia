-- Prove2me | solution 1 for CuspForm.exists_not_dvd_and_smul_mem_twoCuspIntegralSet_integralClosure_of_coe_eq_alSlash_diamondLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/21a8fcd3-024c-5088-9045-8e2f9399d055

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_CuspForm_forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_mem_twoCuspIntegralSet_of_coe_eq_alSlash_diamondLinH
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_mem_twoCuspIntegralSet_two_of_forall_qCoeff_diamondLinH_mem_and_qCoeff_alSlash_diamondLinH_mem
import Theorems.Thm_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH
import Theorems.Thm_CuspForm_exists_linearIndependent_forall_twoCuspLattice_eq_span
import Theorems.Thm_CuspForm_mem_twoCuspIntegralSet_of_mem_twoCuspLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_not_dvd_and_smul_mem_twoCuspIntegralSet_integralClosure_of_coe_eq_alSlash_diamondLinH
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk FreyPackage.ModMCarrier.coe_rescaleLin_apply FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"
p2m_attr_erase "simp" "CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open UpperHalfPlane CongruenceSubgroup

namespace TW2B

def IsLocAt (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (z : ℂ) : Prop :=
  ∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧ (x : ℂ) = y * z

theorem isLocAt_of_mem {𝔪 : Ideal ↥(integralClosure ℤ ℂ)} (h𝔪 : 𝔪 ≠ ⊤) {z : ℂ} (hz : z ∈ integralClosure ℤ ℂ) : IsLocAt 𝔪 z :=
  ⟨⟨z, hz⟩, 1, (Ideal.ne_top_iff_one 𝔪).mp h𝔪, by simp⟩

def loc (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) : Subring ℂ where
  carrier := {z | IsLocAt 𝔪 z}
  mul_mem' := by
    rintro z₁ z₂ ⟨x₁, y₁, hy₁, h₁⟩ ⟨x₂, y₂, hy₂, h₂⟩
    refine ⟨x₁ * x₂, y₁ * y₂, fun h => (h𝔪.mem_or_mem h).elim hy₁ hy₂, ?_⟩
    push_cast; rw [h₁, h₂]; ring
  one_mem' := ⟨1, 1, (Ideal.ne_top_iff_one 𝔪).mp h𝔪.ne_top, by simp⟩
  add_mem' := by
    rintro z₁ z₂ ⟨x₁, y₁, hy₁, h₁⟩ ⟨x₂, y₂, hy₂, h₂⟩
    refine ⟨x₁ * y₂ + x₂ * y₁, y₁ * y₂, fun h => (h𝔪.mem_or_mem h).elim hy₁ hy₂, ?_⟩
    push_cast; rw [h₁, h₂]; ring
  zero_mem' := ⟨0, 1, (Ideal.ne_top_iff_one 𝔪).mp h𝔪.ne_top, by simp⟩
  neg_mem' := by
    rintro z ⟨x, y, hy, h⟩
    exact ⟨-x, y, hy, by push_cast; rw [h]; ring⟩

theorem mem_loc_iff {𝔪 : Ideal ↥(integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsPrime) {z : ℂ} : z ∈ loc 𝔪 h𝔪 ↔ IsLocAt 𝔪 z := Iff.rfl

def alConjMat {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (A B c D : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a * A + W.b * q * W.R * c - q * W.a * W.R * B - W.b * W.R * D,
     -(W.a * W.b * A) - W.b ^ 2 * W.R * c + q * W.a ^ 2 * B + W.a * W.b * D;
     (q : ℤ) * W.R * (A + q * c - W.R * B - D),
     -(W.R * W.b * A) - q * W.R * W.b * c + q * W.R * W.a * B + q * W.a * D]

theorem det_alConjMat {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (A B c D C : ℤ)
    (hdet : A * D - B * C = 1) (hC : C = q * W.R * c) : (alConjMat W A B c D).det = 1 := by
  have hb := W.bezout
  rw [alConjMat, Matrix.det_fin_two_of]
  linear_combination (-A*D*W.R*W.b + A*D*W.a*q + A*D + B*W.R^2*W.b*c*q - B*W.R*W.a*c*q^2 - B*W.R*c*q) * hb
    + hdet + B * hC

theorem exists_apply_10_eq {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (γ : Gamma0 M) :
    ∃ c : ℤ, ((γ : SL(2, ℤ)) 1 0 : ℤ) = q * W.R * c := by
  have h := Gamma0_mem.mp γ.2
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp h
  exact ⟨c, by rw [hc, W.hM_int]⟩

def alConj {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (σ : Gamma0 M) (c : ℤ)
    (hc : ((σ : SL(2, ℤ)) 1 0 : ℤ) = q * W.R * c) : Gamma0 M :=
  ⟨⟨alConjMat W ((σ : SL(2, ℤ)) 0 0) ((σ : SL(2, ℤ)) 0 1) c ((σ : SL(2, ℤ)) 1 1),
    det_alConjMat W _ _ c _ ((σ : SL(2, ℤ)) 1 0) (by
      have := Matrix.det_fin_two (σ : SL(2, ℤ)).1
      rw [Matrix.SpecialLinearGroup.det_coe] at this
      linear_combination -this) hc⟩, by
    rw [Gamma0_mem]
    show (((q : ℤ) * W.R * (((σ : SL(2, ℤ)) 0 0) + q * c - W.R * ((σ : SL(2, ℤ)) 0 1) - ((σ : SL(2, ℤ)) 1 1)) : ℤ) :
      ZMod M) = 0
    rw [← W.hM_int]; push_cast; simp⟩

theorem mapGL_alConj_mul_alGL {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (σ : Gamma0 M) (c : ℤ)
    (hc : ((σ : SL(2, ℤ)) 1 0 : ℤ) = q * W.R * c) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ((alConj W σ c hc : Gamma0 M) : SL(2, ℤ)) : GL (Fin 2) ℝ) * W.alGL =
      W.alGL * (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  have hb : (q : ℝ) * (W.a : ℝ) - (W.R : ℝ) * (W.b : ℝ) = 1 := by exact_mod_cast W.bezout
  have hcR : ((((σ : SL(2, ℤ)) 1 0 : ℤ)) : ℝ) = (q : ℝ) * (W.R : ℝ) * (c : ℝ) := by exact_mod_cast hc
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alConj, alConjMat, ModularForm.AtkinLehnerDatum.mat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (((σ : SL(2, ℤ)) 0 0 : ℝ) * W.a * q + (W.R : ℝ) * W.b * c * q) * hb + (-(W.b : ℝ)) * hcR
  · linear_combination (((σ : SL(2, ℤ)) 0 1 : ℝ) * W.a * q + ((σ : SL(2, ℤ)) 1 1 : ℝ) * W.b) * hb
  · linear_combination (((σ : SL(2, ℤ)) 0 0 : ℝ) * W.R * q + (W.R : ℝ) * c * q ^ 2) * hb + (-(q : ℝ)) * hcR
  · linear_combination (((σ : SL(2, ℤ)) 0 1 : ℝ) * W.R * q + ((σ : SL(2, ℤ)) 1 1 : ℝ) * q) * hb

theorem hole_dia_alSlash {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ)
    (k : ℤ) (F X : CuspForm (CohCarrier.GammaH M H) k)
    (hX : (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑F) (d : (ZMod M)ˣ) :
    ∃ d' : (ZMod M)ˣ, (⇑(CuspForm.diamondLinH k d X) : UpperHalfPlane → ℂ) =
      ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d' F) := by
  by_cases hD : CuspForm.StableD M H k
  · obtain ⟨c, hc⟩ := exists_apply_10_eq W (CuspForm.gammaLift M d)
    refine ⟨CohCarrier.gamma0Units M (alConj W (CuspForm.gammaLift M d) c hc), ?_⟩
    rw [CuspForm.coe_diamondLinH_apply k hD d X, hX,
      CuspForm.coe_diamondLinH_eq_slash k hD _ (alConj W (CuspForm.gammaLift M d) c hc) rfl F,
      ModularForm.alSlash_def, ModularForm.alSlash_def, ← SlashAction.slash_mul, ← SlashAction.slash_mul,
      mapGL_alConj_mul_alGL]
  · refine ⟨1, ?_⟩
    have h0 : ∀ d₀ : (ZMod M)ˣ, (CuspForm.diamondLinH k d₀ : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) = 0 := by
      intro d₀; rw [CuspForm.diamondLinH, dif_neg hD]
    rw [h0, h0, LinearMap.zero_apply, LinearMap.zero_apply, ModularForm.alSlash_def]
    simp

def commMat (p Q a b a₂ b₂ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-Q ^ 2 * a₂ ^ 2 * b + Q * a * a₂ * b₂ * p + Q * a * a₂ * p - Q * a₂ * b * p - Q * a₂ * b₂ * p + Q * b₂ ^ 2 * p + Q * b₂ * p - b₂ * p ^ 2,
     Q * a * a₂ ^ 2 * b - Q * a * a₂ * b + Q * a₂ * b ^ 2 - Q * b * b₂ - a ^ 2 * a₂ * b₂ * p + a * a₂ * b₂ * p - a * b₂ ^ 2 * p + b * b₂ * p;
     p * Q * (-Q * a₂ * b - Q * a₂ + Q * b₂ + Q + a * b₂ * p + a * p - b * p - p),
     -Q ^ 2 * b + Q * a * a₂ * b * p + Q * a * a₂ * p - Q * a * b * p - Q * a * b₂ * p + Q * b ^ 2 * p + Q * b * p - a ^ 2 * b₂ * p ^ 2]

theorem det_commMat (p Q a b a₂ b₂ : ℤ) (h1 : p * a - Q * b = 1) (h2 : Q * a₂ - p * b₂ = 1) :
    (commMat p Q a b a₂ b₂).det = 1 := by
  rw [commMat, Matrix.det_fin_two_of]
  linear_combination (-Q ^ 3 * a₂ ^ 2 * b + Q ^ 2 * a * a₂ ^ 2 * p + Q ^ 2 * a₂ ^ 2 + 2 * Q ^ 2 * a₂ * b * b₂ * p - 2 * Q * a * a₂ * b₂ * p ^ 2 - 2 * Q * a₂ * b₂ * p - Q * b * b₂ ^ 2 * p ^ 2 + a * b₂ ^ 2 * p ^ 3 + b₂ ^ 2 * p ^ 2) * h1 + (Q * a₂ - b₂ * p + 1) * h2

theorem commMat_mul (p Q a b a₂ b₂ : ℤ) (h1 : p * a - Q * b = 1) (h2 : Q * a₂ - p * b₂ = 1) :
    commMat p Q a b a₂ b₂ * (!![p * a, b; p * Q, p] * !![Q * a₂, b₂; Q * p, Q]) =
      !![Q * a₂, b₂; Q * p, Q] * !![p * a, b; p * Q, p] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [commMat, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (Q ^ 2 * a * a₂ ^ 2 * p + Q ^ 2 * a₂ * b₂ * p - Q * a * a₂ * b₂ * p ^ 2 - Q * b₂ ^ 2 * p ^ 2) * h1 + (Q * a * a₂ * p + Q * b₂ * p) * h2
  · linear_combination (Q ^ 2 * a₂ ^ 2 * b - Q * a₂ * b * b₂ * p + Q * a₂ * b₂ * p - b₂ ^ 2 * p ^ 2) * h1 + (Q * a₂ * b + b₂ * p) * h2
  · linear_combination (Q ^ 3 * a₂ * p + Q ^ 2 * a * a₂ * p ^ 2 - Q ^ 2 * b₂ * p ^ 2 - Q * a * b₂ * p ^ 3) * h1 + (Q ^ 2 * p + Q * a * p ^ 2) * h2
  · linear_combination (Q ^ 2 * a₂ * b * p + Q ^ 2 * a₂ * p - Q * b * b₂ * p ^ 2 - Q * b₂ * p ^ 2) * h1 + (Q * b * p + Q * p) * h2

theorem dvd_commMat_10 (p Q a b a₂ b₂ : ℤ) : p * Q ∣ commMat p Q a b a₂ b₂ 1 0 := Dvd.intro _ rfl

theorem hole_alSlash_comm {M p : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p) (V : ModularForm.AtkinLehnerDatum M (M / p)) (k : ℤ)
    (F : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ δ : (ZMod M)ˣ, ModularForm.alSlash W k (ModularForm.alSlash V k ⇑F) =
      ModularForm.alSlash V k (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k δ F)) := by
  have hp0 : 0 < p := W.q_pos
  have hQ0 : 0 < M / p := V.q_pos
  have hpM : p ∣ M := Dvd.intro _ W.hM.symm
  have hR : W.R = M / p := by
    calc W.R = p * W.R / p := (Nat.mul_div_cancel_left _ hp0).symm
      _ = M / p := by rw [← W.hM]
  have hR2 : V.R = p :=
    Nat.eq_of_mul_eq_mul_left hQ0 (V.hM.symm.trans (Nat.div_mul_cancel hpM).symm)
  have h1 : (p : ℤ) * W.a - ((M / p : ℕ) : ℤ) * W.b = 1 := by
    have := W.bezout; rw [hR] at this; exact_mod_cast this
  have h2 : ((M / p : ℕ) : ℤ) * V.a - (p : ℤ) * V.b = 1 := by
    have := V.bezout; rw [hR2] at this; exact_mod_cast this
  let σ : SL(2, ℤ) := ⟨commMat (p : ℤ) ((M / p : ℕ) : ℤ) W.a W.b V.a V.b, det_commMat _ _ _ _ _ _ h1 h2⟩
  have hσ0 : σ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    obtain ⟨c, hc⟩ := dvd_commMat_10 (p : ℤ) ((M / p : ℕ) : ℤ) W.a W.b V.a V.b
    have hM : ((p : ℤ) * ((M / p : ℕ) : ℤ)) = (M : ℤ) := by exact_mod_cast Nat.mul_div_cancel' hpM
    show ((commMat (p : ℤ) ((M / p : ℕ) : ℤ) W.a W.b V.a V.b 1 0 : ℤ) : ZMod M) = 0
    rw [hc, hM]; push_cast; simp
  have hWmat : W.mat = !![(p : ℤ) * W.a, W.b; (p : ℤ) * ((M / p : ℕ) : ℤ), (p : ℤ)] := by
    rw [ModularForm.AtkinLehnerDatum.mat, hR]
  have hVmat : V.mat = !![((M / p : ℕ) : ℤ) * V.a, V.b; ((M / p : ℕ) : ℤ) * (p : ℤ), ((M / p : ℕ) : ℤ)] := by
    rw [ModularForm.AtkinLehnerDatum.mat, hR2]
  have key : (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ) * (W.alGL * V.alGL) = V.alGL * W.alGL := by
    apply Units.ext
    simp only [Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, ModularForm.AtkinLehnerDatum.alGL_coe]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hWmat, hVmat]
    rw [commMat_mul _ _ _ _ _ _ h1 h2]
  have hD : CuspForm.StableD M H k := CuspForm.stableD M H k
  refine ⟨CohCarrier.gamma0Units M ⟨σ, hσ0⟩, ?_⟩
  rw [CuspForm.coe_diamondLinH_eq_slash k hD _ ⟨σ, hσ0⟩ rfl F]
  simp only [ModularForm.alSlash_def, ← SlashAction.slash_mul]
  rw [← key, mul_assoc]

theorem hole_satTest (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : Subring ℂ) (h : CuspForm (CohCarrier.GammaH M H) 2)
    (hS : ∀ (d : (ZMod M)ˣ) (W' : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d h)) n ∈ A ∧
        ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(CuspForm.diamondLinH 2 d h)) n ∈ A) :
    h ∈ CuspForm.twoCuspIntegralSet M H 2 p A :=
  CuspForm.mem_twoCuspIntegralSet_two_of_forall_qCoeff_diamondLinH_mem_and_qCoeff_alSlash_diamondLinH_mem
    p M hpM hpM2 H hHp A h hS

noncomputable def alDatum {p M : ℕ} (hp : p.Prime) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) :
    ModularForm.AtkinLehnerDatum M p where
  R := M / p
  hM := (Nat.mul_div_cancel' hpM).symm
  a := Nat.gcdA p (M / p)
  b := -Nat.gcdB p (M / p)
  bezout := by
    have hcop : Nat.Coprime p (M / p) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpM2 ?_
      obtain ⟨c, hc⟩ := h
      exact ⟨c, by rw [← Nat.mul_div_cancel' hpM, hc]; ring⟩
    have := Nat.gcd_eq_gcd_ab p (M / p)
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    simp only [Nat.cast_one] at this
    linear_combination (-1 : ℤ) * this

theorem diamondLinH_mem_heckeRingH {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (k : ℤ) (d : (ZMod M)ˣ) :
    (CuspForm.diamondLinH k d : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) ∈ CuspForm.heckeRingH M H k :=
  CuspForm.heckeGenH_mem_heckeRingH (∅ : Set ℕ) k (CohCarrier.Gen.dia d)

theorem wallHyp_of_mem_bot {p M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (W₀ : ModularForm.AtkinLehnerDatum M p)
    {g : CuspForm (CohCarrier.GammaH M H) 2} (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪 ≠ ⊤) (n : ℕ) :
    ∃ x y : ↥(integralClosure ℤ ℂ), y ∉ 𝔪 ∧ (x : ℂ) = y * (UpperHalfPlane.qExpansion 1 ⇑g).coeff n := by
  have h1 := (hg 1 (Subring.one_mem _) W₀ n).1
  rw [Module.End.one_apply] at h1
  obtain ⟨r, hr⟩ := Subring.mem_bot.mp h1
  refine ⟨(r : ↥(integralClosure ℤ ℂ)), 1, (Ideal.ne_top_iff_one 𝔪).mp h𝔪, ?_⟩
  push_cast
  rw [one_mul, hr]
  rfl

theorem hHp_introLeft {p M : ℕ} (hp : p.Prime) {H : Subgroup (ZMod M)ˣ} (hpM : p ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M p) :
    ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := by
  have hR : W.R = M / p := by
    calc W.R = p * W.R / p := (Nat.mul_div_cancel_left _ hp.pos).symm
      _ = M / p := by rw [← W.hM]
  intro u hu
  apply hHp u
  have key : ∀ (d : ℕ) (hd : d ∣ M), d = M / p → ZMod.unitsMap hd u = 1 →
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 := by
    intro d hd hdd h; subst hdd; exact h
  exact key W.R _ hR hu

theorem beta_inf_dia
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (X : CuspForm (CohCarrier.GammaH M H) 2)
    (hX : (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪) (d : (ZMod M)ˣ) (n : ℕ) :
    IsLocAt 𝔪 (ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d X)) n) := by
  have hp : p.Prime := Fact.out
  obtain ⟨d', hd'⟩ := hole_dia_alSlash Wd H 2 (CuspForm.diamondLinH 2 e f) X hX d
  set F' : CuspForm (CohCarrier.GammaH M H) 2 := CuspForm.diamondLinH 2 d' (CuspForm.diamondLinH 2 e f) with hF'
  have hF'mem : F' ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (diamondLinH_mem_heckeRingH 2 d')
      (CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (diamondLinH_mem_heckeRingH 2 e) hf)
  obtain ⟨x, y, hy, hxy⟩ :=
    CuspForm.forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even p M H hpM hpM2 hHp Wd F'
      even_two 𝔪 h𝔪 hp𝔪
      (wallHyp_of_mem_bot (alDatum hp hpM hpM2) hF'mem 𝔪 h𝔪.ne_top) n
  refine ⟨x, y, hy, ?_⟩
  rw [hxy, hd']
  rfl

theorem beta_W_dia
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (X : CuspForm (CohCarrier.GammaH M H) 2)
    (hX : (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪) (d : (ZMod M)ˣ)
    (W' : ModularForm.AtkinLehnerDatum M p) (n : ℕ) :
    IsLocAt 𝔪 (ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(CuspForm.diamondLinH 2 d X)) n) := by
  have hp : p.Prime := Fact.out
  obtain ⟨d', hd'⟩ := hole_dia_alSlash Wd H 2 (CuspForm.diamondLinH 2 e f) X hX d
  set F' : CuspForm (CohCarrier.GammaH M H) 2 := CuspForm.diamondLinH 2 d' (CuspForm.diamondLinH 2 e f) with hF'
  have hF'mem : F' ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (diamondLinH_mem_heckeRingH 2 d')
      (CuspForm.heckeRingH_apply_mem_twoCuspIntegralSet (diamondLinH_mem_heckeRingH 2 e) hf)

  obtain ⟨δ, hδ⟩ := hole_alSlash_comm H W' Wd 2 F'

  obtain ⟨G, hG⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W' H (hHp_introLeft hp hpM hHp W') 2
    (CuspForm.diamondLinH 2 δ F')
  have hGmem : G ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) :=
    CuspForm.mem_twoCuspIntegralSet_of_coe_eq_alSlash_diamondLinH p M hpM hpM2 H hHp W' δ F' hF'mem G hG
  obtain ⟨x, y, hy, hxy⟩ :=
    CuspForm.forall_exists_eq_mul_qExpansion_alSlash_of_mem_maximal_of_forall_unitsMap_of_even p M H hpM hpM2 hHp Wd G
      even_two 𝔪 h𝔪 hp𝔪
      (wallHyp_of_mem_bot W' hGmem 𝔪 h𝔪.ne_top) n
  refine ⟨x, y, hy, ?_⟩
  rw [hxy, hd', hδ, hG]
  rfl

theorem seam_beta_loc
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (X : CuspForm (CohCarrier.GammaH M H) 2)
    (hX : (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪) :
    X ∈ CuspForm.twoCuspIntegralSet M H 2 p (loc 𝔪 h𝔪.isPrime) :=
  hole_satTest p M hpM hpM2 H hHp (loc 𝔪 h𝔪.isPrime) X fun d W' n =>
    ⟨beta_inf_dia p M H hpM hpM2 hHp Wd e f hf X hX 𝔪 h𝔪 hp𝔪 d n, beta_W_dia p M H hpM hpM2 hHp Wd e f hf X hX 𝔪 h𝔪 hp𝔪 d W' n⟩

theorem ordCompl_mul_mem_integralClosure_of_isLocAt {p : ℕ} (hp : p.Prime) {z : ℂ} {D : ℕ}
    (h1 : (D : ℂ) * z ∈ integralClosure ℤ ℂ)
    (hloc : ∀ 𝔪 : Ideal ↥(integralClosure ℤ ℂ), 𝔪.IsMaximal → ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪 → IsLocAt 𝔪 z) :
    ((D / p ^ D.factorization p : ℕ) : ℂ) * z ∈ integralClosure ℤ ℂ := by
  set a : ℕ := D.factorization p with ha
  set D' : ℕ := D / p ^ a with hD'
  have hpD : p ^ a * D' = D := Nat.ordProj_mul_ordCompl_eq_self D p
  set w : ℂ := (D' : ℂ) * z with hw

  let I : Ideal ↥(integralClosure ℤ ℂ) :=
    { carrier := {y | (y : ℂ) * w ∈ integralClosure ℤ ℂ}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        push_cast; rw [add_mul]; exact add_mem hu hv
      zero_mem' := by simp only [Set.mem_setOf_eq]; push_cast; rw [zero_mul]; exact zero_mem _
      smul_mem' := fun c {u} hu => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hu ⊢
        push_cast; rw [mul_assoc]; exact mul_mem c.2 hu }
  have hI : ∀ y : ↥(integralClosure ℤ ℂ), y ∈ I ↔ (y : ℂ) * w ∈ integralClosure ℤ ℂ := fun y => Iff.rfl

  have hpa : (((p : ℤ) : ↥(integralClosure ℤ ℂ)) ^ a) ∈ I := by
    rw [hI]; push_cast
    have : ((p : ℂ) ^ a) * w = (D : ℂ) * z := by
      rw [hw, ← mul_assoc, ← hpD]; push_cast; ring
    rw [this]; exact h1

  by_contra hcon
  have hI1 : (1 : ↥(integralClosure ℤ ℂ)) ∉ I := by
    intro h; apply hcon; have := (hI 1).mp h; simpa using this
  have hItop : I ≠ ⊤ := fun h => hI1 (h ▸ Submodule.mem_top)
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hItop
  have hp𝔪 : ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪 := h𝔪.isPrime.mem_of_pow_mem a (hI𝔪 hpa)
  obtain ⟨x, y, hy, hxy⟩ := hloc 𝔪 h𝔪 hp𝔪
  apply hy
  apply hI𝔪
  rw [hI, hw, show (y : ℂ) * ((D' : ℂ) * z) = (D' : ℂ) * ((y : ℂ) * z) by ring, ← hxy]
  exact mul_mem (natCast_mem _ D') x.2

theorem one_mem_strictPeriods_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularCurve.translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_smul_of_analyticAt {F : UpperHalfPlane → ℂ} (hF : AnalyticAt ℂ (cuspFunction 1 F) 0)
    (c : ℂ) (n : ℕ) :
    ModularFormClass.qCoeff (c • F) n = c * ModularFormClass.qCoeff F n := by
  unfold ModularFormClass.qCoeff
  rw [qExpansion_smul hF c, map_smul, smul_eq_mul]

theorem analyticAt_cuspFunction_coe {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}
    (Y : CuspForm (CohCarrier.GammaH M H) k) : AnalyticAt ℂ (cuspFunction 1 (⇑Y)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero Y one_pos (one_mem_strictPeriods_GammaH M H)

def alConjT {M q : ℕ} (W' : ModularForm.AtkinLehnerDatum M q) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1 - (q : ℤ) * W'.a * W'.R, (q : ℤ) * W'.a ^ 2; -((q : ℤ) * (W'.R : ℤ) ^ 2), 1 + (q : ℤ) * W'.a * W'.R]

theorem det_alConjT {M q : ℕ} (W' : ModularForm.AtkinLehnerDatum M q) : (alConjT W').det = 1 := by
  rw [alConjT, Matrix.det_fin_two_of]; ring

def alConjTSL {M q : ℕ} (W' : ModularForm.AtkinLehnerDatum M q) : SL(2, ℤ) := ⟨alConjT W', det_alConjT W'⟩

theorem alConjTSL_mem_Gamma1 {M q : ℕ} (W' : ModularForm.AtkinLehnerDatum M q) : alConjTSL W' ∈ Gamma1 M := by
  rw [Gamma1_mem]
  have hM : (M : ℤ) = q * W'.R := W'.hM_int
  have h1 : ((q : ℤ) * W'.a * W'.R : ℤ) = (M : ℤ) * W'.a := by rw [hM]; ring
  have h2 : ((q : ℤ) * (W'.R : ℤ) ^ 2 : ℤ) = (M : ℤ) * W'.R := by rw [hM]; ring
  refine ⟨?_, ?_, ?_⟩
  · show (((1 - (q : ℤ) * W'.a * W'.R : ℤ)) : ZMod M) = 1
    rw [h1]; push_cast; simp
  · show (((1 + (q : ℤ) * W'.a * W'.R : ℤ)) : ZMod M) = 1
    rw [h1]; push_cast; simp
  · show (((-((q : ℤ) * (W'.R : ℤ) ^ 2) : ℤ)) : ZMod M) = 0
    rw [h2]; push_cast; simp

theorem mapGL_alConjTSL_mul_alGL {M q : ℕ} [NeZero M] (W' : ModularForm.AtkinLehnerDatum M q) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (alConjTSL W') : GL (Fin 2) ℝ) * W'.alGL =
      W'.alGL * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
  have hb : (q : ℝ) * (W'.a : ℝ) - (W'.R : ℝ) * (W'.b : ℝ) = 1 := by exact_mod_cast W'.bezout
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alConjTSL, alConjT, ModularForm.AtkinLehnerDatum.mat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.upperRightHom_apply]
  · ring
  · linear_combination ((q : ℝ) * W'.a) * hb
  · ring
  · linear_combination ((q : ℝ) * W'.R) * hb

open ConjAct Pointwise in
theorem one_mem_strictPeriods_conj_alGL {M q : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (W' : ModularForm.AtkinLehnerDatum M q) :
    (1 : ℝ) ∈ (toConjAct W'.alGL⁻¹ •
      ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul,
    ← mapGL_alConjTSL_mul_alGL, mul_inv_cancel_right]
  exact Subgroup.mem_map_of_mem _ (ModularCurve.Gamma1_le_GammaH M H (alConjTSL_mem_Gamma1 W'))

theorem analyticAt_cuspFunction_alSlash {M q : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ}
    (W' : ModularForm.AtkinLehnerDatum M q) (Y : CuspForm (CohCarrier.GammaH M H) k) :
    AnalyticAt ℂ (cuspFunction 1 (ModularForm.alSlash W' k ⇑Y)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero (CuspForm.translate Y W'.alGL) one_pos
    (one_mem_strictPeriods_conj_alGL H W')

noncomputable def atkinLehnerDatumOfNotSqDvd (p M : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) :
    ModularForm.AtkinLehnerDatum M p where
  R := M / p
  hM := (Nat.mul_div_cancel' hpM).symm
  a := Nat.gcdA p (M / p)
  b := - Nat.gcdB p (M / p)
  bezout := by
    have hcop : Nat.Coprime p (M / p) := by
      refine (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr ?_
      intro h; apply hpM2
      obtain ⟨m, hm⟩ := h
      exact ⟨m, by rw [pow_two, mul_assoc, ← hm, Nat.mul_div_cancel' hpM]⟩
    have h := Nat.gcd_eq_gcd_ab p (M / p)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at h
    linear_combination -h

theorem qCoeff_mem_of_mem_twoCuspIntegralSet'
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (A : Subring ℂ) (g : CuspForm (CohCarrier.GammaH M H) 2) (hg : g ∈ CuspForm.twoCuspIntegralSet M H 2 p A) (n : ℕ) :
    ModularFormClass.qCoeff (⇑g) n ∈ A := by
  have h := (hg 1 (CuspForm.heckeRingH M H 2).one_mem (atkinLehnerDatumOfNotSqDvd p M hpM hpM2) n).1
  simpa using h

section SeamGamma

theorem qCoeff_add_of_analyticAt {F G : UpperHalfPlane → ℂ} (hF : AnalyticAt ℂ (cuspFunction 1 F) 0)
    (hG : AnalyticAt ℂ (cuspFunction 1 G) 0) (n : ℕ) :
    ModularFormClass.qCoeff (F + G) n = ModularFormClass.qCoeff F n + ModularFormClass.qCoeff G n := by
  unfold ModularFormClass.qCoeff
  rw [qExpansion_add hF hG, map_add]

theorem qCoeff_coe_sum_smul {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (F : ι → CuspForm (CohCarrier.GammaH M H) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(∑ i ∈ s, c i • F i)) n = ∑ i ∈ s, c i * ModularFormClass.qCoeff (⇑(F i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, CuspForm.coe_zero]
    unfold ModularFormClass.qCoeff
    rw [qExpansion_zero, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add,
      qCoeff_add_of_analyticAt (analyticAt_cuspFunction_coe (c a • F a)) (analyticAt_cuspFunction_coe _) n, ih,
      show (⇑(c a • F a) : UpperHalfPlane → ℂ) = c a • ⇑(F a) from rfl,
      qCoeff_smul_of_analyticAt (analyticAt_cuspFunction_coe (F a))]

theorem qCoeff_alSlash_coe_sum_smul {M q : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ι : Type*}
    (W' : ModularForm.AtkinLehnerDatum M q) (s : Finset ι) (c : ι → ℂ) (F : ι → CuspForm (CohCarrier.GammaH M H) 2) (n : ℕ) :
    ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(∑ i ∈ s, c i • F i)) n =
      ∑ i ∈ s, c i * ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(F i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, CuspForm.coe_zero]
    unfold ModularFormClass.qCoeff
    rw [ModularForm.alSlash_def, SlashAction.zero_slash, qExpansion_zero, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add, ModularForm.alSlash_add,
      qCoeff_add_of_analyticAt (analyticAt_cuspFunction_alSlash W' (c a • F a)) (analyticAt_cuspFunction_alSlash W' _) n,
      ih, show (⇑(c a • F a) : UpperHalfPlane → ℂ) = c a • ⇑(F a) from rfl, ModularForm.alSlash_smul,
      qCoeff_smul_of_analyticAt (analyticAt_cuspFunction_alSlash W' (F a))]

noncomputable def coeffSeq {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] (ℕ → ℂ) where
  toFun F := fun n => ModularFormClass.qCoeff (⇑F) n
  map_add' F G := by
    funext n
    exact (CuspForm.coe_add F G ▸ qCoeff_add_of_analyticAt (analyticAt_cuspFunction_coe F) (analyticAt_cuspFunction_coe G) n :)
  map_smul' c F := by
    funext n
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (⇑(c • F) : UpperHalfPlane → ℂ) = c • ⇑F from rfl]
    exact qCoeff_smul_of_analyticAt (analyticAt_cuspFunction_coe F) c n

theorem coeffSeq_apply {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (F : CuspForm (CohCarrier.GammaH M H) 2) (n : ℕ) :
    coeffSeq F n = ModularFormClass.qCoeff (⇑F) n := rfl

theorem ker_coeffSeq {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} :
    LinearMap.ker (coeffSeq (M := M) (H := H)) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro F hF
  have hΓ := one_mem_strictPeriods_GammaH M H
  haveI : Fact (IsCusp OnePoint.infty ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hq : qExpansion 1 (⇑F) = 0 := by
    ext n
    have h := congrFun hF n
    exact h
  have h0 : (⇑F : UpperHalfPlane → ℂ) = 0 :=
    (qExpansion_eq_zero_iff one_pos (SlashInvariantFormClass.periodic_comp_ofComplex F hΓ)
      (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F)).mp hq
  exact DFunLike.coe_injective (h0.trans CuspForm.coe_zero.symm)

theorem coord_mem_of_forall_mem {K : Type*} [Field K] (k : Subfield K) {ι σ : Type*} [Fintype ι]
    (v : ι → σ → K) (hv : ∀ i n, v i n ∈ k) (hli : LinearIndependent K v)
    (c : ι → K) (hx : ∀ n, (∑ i, c i • v i) n ∈ k) :
    ∀ i, c i ∈ k := by
  classical

  let kK : Submodule k K := (Algebra.ofId k K).range.toSubmodule
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl kK
  let π : K →ₗ[k] kK := Submodule.linearProjOfIsCompl kK Q hQ
  have hπ : ∀ a : k, π (a : K) = ⟨a, ⟨a, rfl⟩⟩ := fun a =>
    Submodule.linearProjOfIsCompl_apply_left hQ ⟨(a : K), ⟨a, rfl⟩⟩

  let ψ : K →ₗ[k] K := LinearMap.id - (kK.subtype.comp π)
  have hψk : ∀ a : k, ψ (a : K) = 0 := by
    intro a; simp [ψ, hπ]
  have hψsmul : ∀ (a : k) (z : K), ψ ((a : K) * z) = (a : K) * ψ z := by
    intro a z
    have : (a : K) * z = a • z := rfl
    rw [this, map_smul]; rfl

  have hrel : ∑ i, ψ (c i) • v i = 0 := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h1 : ψ ((∑ i, c i • v i) n) = 0 := by
      obtain ⟨a, ha⟩ : ∃ a : k, (a : K) = (∑ i, c i • v i) n := ⟨⟨_, hx n⟩, rfl⟩
      rw [← ha, hψk]
    rw [← h1]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_comm (c i), show v i n * c i = ((⟨v i n, hv i n⟩ : k) : K) * c i from rfl, hψsmul, mul_comm]
  intro i
  have h0 : ψ (c i) = 0 := by
    have := Fintype.linearIndependent_iff.mp hli (fun i => ψ (c i)) hrel i
    exact this
  have : c i = (π (c i) : K) := by
    have h := congrArg (fun z => z) h0
    simp only [ψ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.subtype_apply, sub_eq_zero] at h
    exact h
  rw [this]
  obtain ⟨a, ha⟩ := (π (c i)).2
  rw [← ha]
  exact a.2

end SeamGamma

set_option maxHeartbeats 3200000 in

theorem seam_gamma
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (X : CuspForm (CohCarrier.GammaH M H) 2)
    (hX : (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ t ∈ CuspForm.heckeRingH M H 2, ∀ (W' : ModularForm.AtkinLehnerDatum M p) (n : ℕ),
      (D : ℂ) * ModularFormClass.qCoeff (⇑(t X)) n ∈ integralClosure ℤ ℂ ∧
      (D : ℂ) * ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(t X)) n ∈ integralClosure ℤ ℂ := by
  classical

  obtain ⟨r, b, hli, hspan, hlat⟩ :=
    CuspForm.exists_linearIndependent_forall_twoCuspLattice_eq_span p M hpM hpM2 H hHp

  have hbset : ∀ i, b i ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ) := by
    intro i
    refine CuspForm.mem_twoCuspIntegralSet_of_mem_twoCuspLattice p M hpM H hHp (b i) ?_
    rw [hlat ⊥]
    exact Submodule.subset_span ⟨i, rfl⟩

  obtain ⟨c, hc⟩ : ∃ c : Fin r → ℂ, ∑ i, c i • b i = X := by
    rw [← Submodule.mem_span_range_iff_exists_fun ℂ, hspan]; trivial

  let k : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield
  have hk : ∀ z : ℂ, z ∈ k ↔ IsAlgebraic ℚ z := fun z => mem_algebraicClosure_iff

  let v : Fin r → ℕ → ℂ := fun i n => ModularFormClass.qCoeff (⇑(b i)) n
  have hvZ : ∀ i n, v i n ∈ (⊥ : Subring ℂ) := fun i n =>
    qCoeff_mem_of_mem_twoCuspIntegralSet' p M H hpM hpM2 ⊥ (b i) (hbset i) n
  have hv : ∀ i n, v i n ∈ k := by
    intro i n
    obtain ⟨z, hz⟩ := Subring.mem_bot.mp (hvZ i n)
    rw [hk, ← hz]
    exact isAlgebraic_int z
  have hliv : LinearIndependent ℂ v := by
    have h := hli.map' coeffSeq ker_coeffSeq
    exact h

  have hxv : (∑ i, c i • v i) = fun n => ModularFormClass.qCoeff (⇑X) n := by
    have h := congrArg coeffSeq hc
    rw [map_sum] at h
    simp only [map_smul] at h
    funext n
    have h' := congrFun h n
    simpa [Finset.sum_apply, Pi.smul_apply, coeffSeq_apply] using h'
  obtain ⟨D₀, hD₀, hint⟩ :=
    CuspForm.exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH p M H hpM hpM2 Wd e f hf
  have hxk : ∀ n, ModularFormClass.qCoeff (⇑X) n ∈ k := by
    intro n
    have hI : IsIntegral ℤ ((D₀ : ℂ) * ModularFormClass.qCoeff (⇑X) n) := by
      unfold ModularFormClass.qCoeff
      rw [hX]
      exact hint n
    have hmem : (D₀ : ℂ) * ModularFormClass.qCoeff (⇑X) n ∈ k :=
      (hk _).mpr ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hI.isAlgebraic)
    have hD₀C : (D₀ : ℂ) ≠ 0 := by exact_mod_cast hD₀
    have : ModularFormClass.qCoeff (⇑X) n = ((D₀ : ℂ))⁻¹ * ((D₀ : ℂ) * ModularFormClass.qCoeff (⇑X) n) := by
      rw [← mul_assoc, inv_mul_cancel₀ hD₀C, one_mul]
    rw [this]
    exact mul_mem (inv_mem (natCast_mem k D₀)) hmem

  have hck : ∀ i, c i ∈ k :=
    coord_mem_of_forall_mem k v hv hliv c (fun n => by rw [hxv]; exact hxk n)

  have hN : ∀ i, ∃ N : ℤ, N ≠ 0 ∧ (N : ℂ) * c i ∈ integralClosure ℤ ℂ := by
    intro i
    have ha : IsAlgebraic ℤ (c i) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr ((hk _).mp (hck i))
    obtain ⟨y, hy, hI⟩ := ha.exists_integral_multiple
    refine ⟨y, hy, ?_⟩
    rw [mem_integralClosure_iff, ← zsmul_eq_mul]
    exact hI
  choose N hN0 hNint using hN
  let P : ℤ := ∏ i, N i
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hN0 i)
  have hPc : ∀ i, (P : ℂ) * c i ∈ integralClosure ℤ ℂ := by
    intro i
    have : (P : ℂ) * c i = (∏ j ∈ Finset.univ.erase i, (N j : ℂ)) * ((N i : ℂ) * c i) := by
      simp only [P, Int.cast_prod]
      rw [← mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [this]
    exact mul_mem (prod_mem (fun j _ => intCast_mem _ (N j))) (hNint i)
  refine ⟨P.natAbs, Int.natAbs_ne_zero.mpr hP0, fun t ht W' n => ?_⟩
  have hDc : ∀ i, ((P.natAbs : ℕ) : ℂ) * c i ∈ integralClosure ℤ ℂ := by
    intro i
    have hcast : ((P.natAbs : ℕ) : ℂ) = ((P.natAbs : ℤ) : ℂ) := (Int.cast_natCast _).symm
    by_cases hP : 0 ≤ P
    · rw [hcast, Int.natAbs_of_nonneg hP]; exact hPc i
    · rw [hcast, Int.ofNat_natAbs_of_nonpos (le_of_lt (not_le.mp hP)), Int.cast_neg, neg_mul]
      exact neg_mem (hPc i)

  have htX : t X = ∑ i, c i • t (b i) := by
    rw [← hc, map_sum]
    simp only [map_smul]

  have hZ : ∀ i, ModularFormClass.qCoeff (⇑(t (b i))) n ∈ integralClosure ℤ ℂ ∧
      ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(t (b i))) n ∈ integralClosure ℤ ℂ := by
    intro i
    obtain ⟨h1, h2⟩ := hbset i t ht W' n
    obtain ⟨z1, hz1⟩ := Subring.mem_bot.mp h1
    obtain ⟨z2, hz2⟩ := Subring.mem_bot.mp h2
    exact ⟨hz1 ▸ intCast_mem _ z1, hz2 ▸ intCast_mem _ z2⟩
  refine ⟨?_, ?_⟩
  · rw [htX, qCoeff_coe_sum_smul, Finset.mul_sum]
    refine sum_mem (fun i _ => ?_)
    rw [← mul_assoc]
    exact mul_mem (hDc i) (hZ i).1
  · rw [htX, qCoeff_alSlash_coe_sum_smul, Finset.mul_sum]
    refine sum_mem (fun i _ => ?_)
    rw [← mul_assoc]
    exact mul_mem (hDc i) (hZ i).2

end TW2B

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (X : CuspForm (CohCarrier.GammaH M H) 2)
    (hX : (⇑X : UpperHalfPlane → ℂ) = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) :
    ∃ D : ℕ, ¬ p ∣ D ∧
      ((D : ℂ) • X : CuspForm (CohCarrier.GammaH M H) 2) ∈
        CuspForm.twoCuspIntegralSet M H 2 p (integralClosure ℤ ℂ).toSubring := by
  have hp : p.Prime := Fact.out
  obtain ⟨D, hD0, hD⟩ := TW2B.seam_gamma p M H hpM hpM2 hHp Wd e f hf X hX
  have hβ := TW2B.seam_beta_loc p M H hpM hpM2 hHp Wd e f hf X hX
  refine ⟨D / p ^ D.factorization p, Nat.not_dvd_ordCompl hp hD0, ?_⟩
  set D' : ℕ := D / p ^ D.factorization p with hD'
  intro t ht W' n
  obtain ⟨hD1, hD2⟩ := hD t ht W' n
  have hloc1 : ∀ 𝔪 : Ideal ↥(integralClosure ℤ ℂ), 𝔪.IsMaximal → ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪 →
      TW2B.IsLocAt 𝔪 (ModularFormClass.qCoeff (⇑(t X)) n) :=
    fun 𝔪 h𝔪 hp𝔪 => (hβ 𝔪 h𝔪 hp𝔪 t ht W' n).1
  have hloc2 : ∀ 𝔪 : Ideal ↥(integralClosure ℤ ℂ), 𝔪.IsMaximal → ((p : ℤ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪 →
      TW2B.IsLocAt 𝔪 (ModularFormClass.qCoeff (ModularForm.alSlash W' 2 ⇑(t X)) n) :=
    fun 𝔪 h𝔪 hp𝔪 => (hβ 𝔪 h𝔪 hp𝔪 t ht W' n).2
  have htX : t ((D' : ℂ) • X) = (D' : ℂ) • t X := map_smul t (D' : ℂ) X
  have hcoe : (⇑(t ((D' : ℂ) • X)) : UpperHalfPlane → ℂ) = (D' : ℂ) • ⇑(t X) := by
    rw [htX, CuspForm.IsGLPos.coe_smul]
  refine ⟨?_, ?_⟩
  · rw [Subalgebra.mem_toSubring, hcoe,
      TW2B.qCoeff_smul_of_analyticAt (TW2B.analyticAt_cuspFunction_coe (t X)) (D' : ℂ) n]
    exact TW2B.ordCompl_mul_mem_integralClosure_of_isLocAt hp hD1 hloc1
  · rw [Subalgebra.mem_toSubring, hcoe, ModularForm.alSlash_smul,
      TW2B.qCoeff_smul_of_analyticAt (TW2B.analyticAt_cuspFunction_alSlash W' (t X)) (D' : ℂ) n]
    exact TW2B.ordCompl_mul_mem_integralClosure_of_isLocAt hp hD2 hloc2

end S_CuspForm_exists_not_dvd_and_smul_mem_twoCuspIntegralSet_integralClosure_of_coe_eq_alSlash_diamondLinH
end P2MW
export P2MW.S_CuspForm_exists_not_dvd_and_smul_mem_twoCuspIntegralSet_integralClosure_of_coe_eq_alSlash_diamondLinH (solution)

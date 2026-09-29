-- Prove2me | solution 1 for CuspForm.exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9e6835b2-bec6-5d6b-a151-c662efb653ff

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_XH
import Definitions.Def_CohCarrier_Level
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Theorems.Thm_ModularCurve_laurentBaseChange_adjoin
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq
import Theorems.Thm_AlgebraicCurve_exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open UpperHalfPlane HahnSeries
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH Gamma1_le_GammaH restrictForm IsIntegralQExp intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset jq coeff_jq_neg_one jq_mem coeffMap coeffMap_coeff algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqModC_rat map_jqModC qEuler qEuler_coeff instAlgebraIntermediateFieldLaurent diffQExp diffQExp_smul_D thetaL thetaL_apply jqModC_eq_qExpansion_E4_cube_div_discriminant qExpansion_div_mem_laurentBaseChange_xHFunctionField mem_of_coeffEmb_mem_laurentBaseChange jqModC_mem_intFormRatiosC mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange laurentBaseChange_adjoin exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed transcendental_jqModC smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq"
namespace M1Body
p2m_open "ModularCurve"

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

def thetaPS (p : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n : ℕ => (n : R) * PowerSeries.coeff n p

theorem thetaPS_eq (p : PowerSeries R) :
    thetaPS p = PowerSeries.mk fun n : ℕ => (n : R) * PowerSeries.coeff n p := rfl

theorem qEuler_ofPowerSeries (p : PowerSeries R) :
    qEuler R (ofPowerSeries ℤ R p) = ofPowerSeries ℤ R (thetaPS p) := by
  ext m
  rw [qEuler_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hm
  · rw [mul_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hm)
    simp [thetaPS, PowerSeries.coeff_mk]

theorem coeffMap_qEuler (f : R →+* S) (x : LaurentSeries R) :
    coeffMap f (qEuler R x) = qEuler S (coeffMap f x) := by
  ext m
  simp

theorem coeffMap_ofPowerSeries_eq (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R p) = ofPowerSeries ℤ S (p.map f) := by
  ext m
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

theorem coeffMap_C (f : R →+* S) (c : R) : coeffMap f (C c) = C (f c) :=
  HahnSeries.map_C c f

end Laurent

section Level

variable {Γ : Subgroup SL(2, ℤ)}

abbrev qL (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem qL_mul (hT : ModularGroup.T ∈ Γ) {a b : ℤ} (f : ModularForm Γ a) (g : ModularForm Γ b) :
    qL (f.mul g) = qL f * qL g := by
  simp only [qL, ModularForm.coe_mul,
    ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods hT), PowerSeries.coe_mul]

theorem qL_mcast {a b : ℤ} (h : a = b) (f : ModularForm Γ a) :
    qL (ModularForm.mcast h f) = qL f := by
  simp only [qL, ModularForm.coe_mcast]

theorem qL_ne_zero (hT : ModularGroup.T ∈ Γ) {k : ℤ} (f : ModularForm Γ k) (hf : f ≠ 0) :
    qL f ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods hT)]
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  simpa [qL] using h

theorem ne_zero_of_qL_ne_zero {k : ℤ} (f : ModularForm Γ k) (h : qL f ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply h
  simp only [qL, ModularForm.coe_zero, UpperHalfPlane.qExpansion_zero (1 : ℝ), PowerSeries.coe_zero]

theorem coe_le_SL (Γ : Subgroup SL(2, ℤ)) : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact ⟨g, rfl⟩

end Level

section LevelOne

def E4cube : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) ((ModularForm.E₄.mul ModularForm.E₄).mul ModularForm.E₄)

theorem coe_E4cube : (E4cube : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) * ModularForm.E₄ * ModularForm.E₄ := by
  simp only [E4cube, ModularForm.coe_mcast, ModularForm.coe_mul]

theorem qL_E4cube : qL E4cube = qL ModularForm.E₄ ^ 3 := by
  rw [coe_E4cube, qL, ← ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos
    one_mem_strictPeriods_SL, ModularForm.coe_mul, ModularForm.qExpansion_mul_coe one_pos
    one_mem_strictPeriods_SL, PowerSeries.coe_mul, PowerSeries.coe_mul]
  ring

def DeltaMF : ModularForm 𝒮ℒ 12 := ModularFormClass.modularForm CuspForm.discriminant

theorem coe_DeltaMF : (DeltaMF : ℍ → ℂ) = ModularForm.discriminant := rfl

theorem DeltaMF_apply_ne_zero (z : ℍ) : DeltaMF z ≠ 0 := by
  rw [coe_DeltaMF]
  exact ModularForm.discriminant_ne_zero z

end LevelOne

section Ext

p2m_attr_erase "instance" "DivisionRing.toRatAlgebra"

variable (Γ : Subgroup SL(2, ℤ))

local notation "ℚb" => AlgebraicClosure ℚ
local notation "FQ" => ModularCurve.qExpFunctionFieldC ℚ Γ
local notation "FB" => ModularCurve.qExpFunctionFieldC (AlgebraicClosure ℚ) Γ

theorem coeffEmb_rat (x : LaurentSeries ℚ) : coeffEmb ℚ x = x := by
  ext n; simp [coeffEmb_coeff]

theorem eq_laurentBaseChange_rat : (FQ) = laurentBaseChange ℚ FQ := by
  rw [qExpFunctionFieldC, ModularCurve.laurentBaseChange_adjoin]
  congr 1
  ext x
  simp [coeffEmb_rat]

theorem coeffEmb_intSeriesC' (L : Type*) [Field L] [Algebra ℚ L] (p : PowerSeries ℤ) : coeffEmb L (intSeriesC ℚ p) = intSeriesC L p := by
  rw [coeffEmb, intSeriesC, coeffMap_ofPowerSeries_eq, intSeriesC]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem coeffEmb_injective' (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (coeffEmb L) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries L => s.coeff n) h
  simp only [coeffEmb_coeff] at h1
  exact (algebraMap ℚ L).injective h1

theorem image_intFormRatiosC' (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L '' intFormRatiosC ℚ Γ = intFormRatiosC L Γ := by
  ext z
  constructor
  · rintro ⟨_, ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    have hgL : intSeriesC L pg ≠ 0 := by
      rw [← coeffEmb_intSeriesC' L]
      exact (map_ne_zero_iff _ (coeffEmb_injective' L)).mpr hg0
    refine ⟨κ, f, g, pf, pg, hf, hg, hgL, ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC', coeffEmb_intSeriesC']
  · rintro ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩
    have hgQ : intSeriesC ℚ pg ≠ 0 := by
      intro h
      apply hg0
      rw [← coeffEmb_intSeriesC' L, h, map_zero]
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨κ, f, g, pf, pg, hf, hg, hgQ, rfl⟩, ?_⟩
    rw [map_div₀, coeffEmb_intSeriesC', coeffEmb_intSeriesC']

theorem laurentBaseChange_bar : laurentBaseChange ℚb FQ = FB := by
  rw [qExpFunctionFieldC, ModularCurve.laurentBaseChange_adjoin, image_intFormRatiosC']
  rfl

theorem thetaL_eq_qEuler' (L : Type*) [Field L] (x : LaurentSeries L) : thetaL L x = qEuler L x := by
  ext n
  rw [thetaL_apply, coeff_single_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, qEuler_coeff, Nat.cast_one, sub_add_cancel,
    Ring.choose_one_right, one_mul, zsmul_eq_mul]

theorem coeffEmb_mem_bar {x : LaurentSeries ℚ} (hx : x ∈ FQ) : coeffEmb ℚb x ∈ FB := by
  have h := coeffEmb_mem_laurentBaseChange (L := ℚb) hx
  rw [laurentBaseChange_bar] at h
  exact h

def emb : ↥FQ →+* ↥FB where
  toFun x := ⟨coeffEmb ℚb (x : LaurentSeries ℚ), coeffEmb_mem_bar Γ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_emb (x : ↥FQ) : ((emb Γ x : ↥FB) : LaurentSeries ℚb) = coeffEmb ℚb (x : LaurentSeries ℚ) := rfl

theorem isPrincipalIdealRing_of_ne_top [Γ.FiniteIndex] (hT' : ModularGroup.T ∈ Γ)
    (O : ValuationSubring ↥FQ) (hO : ∀ a : ℚ, algebraMap ℚ ↥FQ a ∈ O) (hO' : O ≠ ⊤) : IsPrincipalIdealRing O := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ↥FQ, (j₀ : LaurentSeries ℚ) = jq := by
    refine ⟨⟨jq, ?_⟩, rfl⟩
    have h := intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ)
    rwa [jqModC_rat] at h
  haveI : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j₀} : Set ↥FQ)) ↥FQ := by
    have h := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange Γ hT' ℚ FQ
      (eq_laurentBaseChange_rat Γ) j₀ (by rw [hj₀]; ext n; simp [coeffEmb_coeff])
    convert h <;> exact Subsingleton.elim _ _
  exact ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin j₀ O hO hO'

end Ext

section MainQ

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "ΓH" => CohCarrier.GammaH M H

scoped instance finiteIndex_GammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H

theorem jq_mem : (jq : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ ΓH := by
  have h := intFormRatiosC_subset ℚ ΓH (ModularCurve.jqModC_mem_intFormRatiosC ℚ ΓH)
  rwa [jqModC_rat] at h

theorem qEuler_jq_ne_zero : qEuler ℚ jq ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : LaurentSeries ℚ => x.coeff (-1)) h
  simp only [qEuler_coeff, coeff_jq_neg_one, mul_one, HahnSeries.coeff_zero, Int.cast_neg, Int.cast_one, neg_eq_zero,
    one_ne_zero] at h1

def fQ (pf : PowerSeries ℤ) : LaurentSeries ℚ := intSeriesC ℚ pf

theorem coeffEmb_fQ (f : CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2) (pf : PowerSeries ℤ) (hpf : IsIntegralQExp f pf) : coeffEmb ℂ (fQ pf) = qL f := by
  have hmm : PowerSeries.map (algebraMap ℚ ℂ) (pf.map (Int.castRingHom ℚ)) = pf.map (Int.castRingHom ℂ) := by
    ext n
    simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]
  rw [fQ, intSeriesC, coeffEmb, coeffMap_ofPowerSeries_eq, hmm, hpf]

def xQ (pf : PowerSeries ℤ) : LaurentSeries ℚ := fQ pf / qEuler ℚ jq

theorem xQ_mul_qEuler_jq (pf : PowerSeries ℤ) : xQ pf * qEuler ℚ jq = fQ pf := div_mul_cancel₀ _ qEuler_jq_ne_zero

theorem exists_coeffEmb_xQ_eq_div (f : CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2) (pf : PowerSeries ℤ) (hpf : IsIntegralQExp f pf) :
    ∃ (G B : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) (12 + 12 + 2)), B ≠ 0 ∧
      coeffEmb ℂ (C (12 : ℚ)⁻¹ * xQ pf) = qL G / qL B := by
  have hT' := hT M H
  let G : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 12 := restrictForm (coe_le_SL _) E4cube
  let Dl : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 12 := restrictForm (coe_le_SL _) DeltaMF
  have hG : (G : ℍ → ℂ) = E4cube := rfl
  have hDl : (Dl : ℍ → ℂ) = DeltaMF := rfl
  obtain ⟨B, -, hB⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq
    (Γ := CohCarrier.GammaH M H) (one_mem_strictPeriods hT') Dl G
  set a : LaurentSeries ℂ := qL G with ha
  set b : LaurentSeries ℂ := qL Dl with hb
  set Da : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (thetaPS (qExpansion 1 G)) with hDa
  set Db : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (thetaPS (qExpansion 1 Dl)) with hDb
  set W : LaurentSeries ℂ := b * Da - Db * a with hW
  have hDl0 : Dl ≠ 0 := by
    intro h0
    have := congrArg (fun F : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 12 => (F : ℍ → ℂ) I) h0
    simp only [hDl, ModularForm.coe_zero, Pi.zero_apply] at this
    exact DeltaMF_apply_ne_zero I this
  have hb0 : b ≠ 0 := qL_ne_zero hT' Dl hDl0
  have hBq : qL B = C (12 : ℂ) * W := by
    rw [qL, hB]
    simp only [map_sub, map_mul, ofPowerSeries_C, ← thetaPS_eq]
    push_cast
    ring
  have hj : coeffEmb ℂ (jq : LaurentSeries ℚ) = a / b := by
    have e1 : coeffEmb ℂ (jq : LaurentSeries ℚ) = jqModC ℂ := by
      rw [coeffEmb, ← jqModC_rat]
      exact map_jqModC _
    rw [e1, ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, ha, hb, hG, hDl, qL_E4cube, coe_DeltaMF]
  have hTh : coeffEmb ℂ (qEuler ℚ jq) = b⁻¹ ^ 2 * W := by
    rw [coeffEmb, coeffMap_qEuler, ← coeffEmb, hj, Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      ha, hb, qL, qL, qEuler_ofPowerSeries, qEuler_ofPowerSeries, ← hDa, ← hDb, hW]
    ring
  have hT0 : coeffEmb ℂ (qEuler ℚ jq) ≠ 0 := (map_ne_zero (coeffEmb ℂ)).mpr qEuler_jq_ne_zero
  have hW0 : W ≠ 0 := by
    intro hW0
    apply hT0
    rw [hTh, hW0, mul_zero]
  have hB0 : B ≠ 0 := by
    refine ne_zero_of_qL_ne_zero B ?_
    rw [hBq]
    exact mul_ne_zero (C_ne_zero (by norm_num)) hW0
  let Fm : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2 := ModularFormClass.modularForm f
  let Gnum : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) (12 + 12 + 2) :=
    ModularForm.mcast (by norm_num) ((Fm.mul Dl).mul Dl)
  have hGnum : qL Gnum = qL f * b * b := by
    simp only [Gnum, qL_mcast, qL_mul hT', hb]
    rfl
  refine ⟨Gnum, B, hB0, ?_⟩
  have hc : (C (12 : ℂ) : LaurentSeries ℂ) ≠ 0 := C_ne_zero (by norm_num)
  have e12 : coeffEmb ℂ (C (12 : ℚ)) = C (12 : ℂ) := by
    rw [coeffEmb, coeffMap_C, map_ofNat]
  rw [map_mul, map_inv₀, map_inv₀, e12, xQ, map_div₀, coeffEmb_fQ M H f pf hpf, hTh, hGnum, hBq]
  field_simp
  try ring

theorem xQ_mem (f : CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2) (pf : PowerSeries ℤ) (hpf : IsIntegralQExp f pf) : xQ pf ∈ qExpFunctionFieldC ℚ ΓH := by
  obtain ⟨G, B, hB0, hx'⟩ := exists_coeffEmb_xQ_eq_div M H f pf hpf
  have hC : coeffEmb ℂ (C (12 : ℚ)⁻¹ * xQ pf) ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ ΓH) := by
    rw [hx']
    exact ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField M H G B hB0
  have hx'mem : C (12 : ℚ)⁻¹ * xQ pf ∈ qExpFunctionFieldC ℚ ΓH :=
    ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange ℂ (qExpFunctionFieldC ℚ ΓH) _ hC
  have h12 : (12 : ℚ) ≠ 0 := by norm_num
  have hxx : xQ pf = C (12 : ℚ) * (C (12 : ℚ)⁻¹ * xQ pf) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h12, map_one, one_mul]
  rw [hxx]
  refine mul_mem ?_ hx'mem
  have h12mem := (qExpFunctionFieldC ℚ ΓH).algebraMap_mem (12 : ℚ)
  rwa [algebraMap_laurentSeries_eq_single, ← C_apply] at h12mem

theorem exists_pair (f : CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2) (pf : PowerSeries ℤ) (hpf : IsIntegralQExp f pf) :
    ∃ x j : ↥(qExpFunctionFieldC ℚ ΓH), (j : LaurentSeries ℚ) = jq ∧ (x : LaurentSeries ℚ) * qEuler ℚ (j : LaurentSeries ℚ) = intSeriesC ℚ pf :=
  ⟨⟨xQ pf, xQ_mem M H f pf hpf⟩, ⟨jq, jq_mem M H⟩, rfl, xQ_mul_qEuler_jq pf⟩

end MainQ

end ModularCurve.M1Body
p2m_reactivate "P2MW.S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp.ModularCurve P2MW.S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp.ModularCurve.M1Body"
p2m_reactivate "P2MW.S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp.ModularCurve"

end
p2m_reactivate "P2MW.S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp.ModularCurve P2MW.S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp.ModularCurve.M1Body"

p2m_attr_erase "instance" "DivisionRing.toRatAlgebra"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open _root_.ModularCurve _root_.P2MW.S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp.ModularCurve ModularCurve.M1Body in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf) :
    ∃ η : Ω[↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))⁄ℚ],
      ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) η =
        HahnSeries.ofPowerSeries ℤ ℚ (pf.map (Int.castRingHom ℚ)) ∧

      ∀ O : ValuationSubring ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), (∀ a : ℚ, algebraMap ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ O) →
        ∃ c ∈ O, ∃ t ∈ O, η = c • KaehlerDifferential.D ℚ ↥(ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) t := by
  obtain ⟨x, j, hj, hx⟩ := exists_pair M H f pf hpf
  refine ⟨x • KaehlerDifferential.D ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j, ?_, ?_⟩
  ·
    rw [diffQExp_smul_D, hx]
    rfl
  ·
    intro O hO
    by_cases htop : O = ⊤
    · exact ⟨x, by rw [htop]; exact ValuationSubring.mem_top _, j, by rw [htop]; exact ValuationSubring.mem_top _, rfl⟩
    ·
      have hTΓ : ModularGroup.T ∈ CohCarrier.GammaH M H := M1Body.hT M H
      have hpid := M1Body.isPrincipalIdealRing_of_ne_top (CohCarrier.GammaH M H) hTΓ O hO htop
      let v : AlgebraicCurve.Place ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := ⟨O, hO, htop, hpid⟩

      letI algQ : Algebra ℚ ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) := DivisionRing.toRatAlgebra
      haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) := by
        refine ⟨fun q a y => ?_⟩
        simp only [Algebra.smul_def, map_mul, mul_assoc, eq_ratCast, map_ratCast]
      letI alg : Algebra ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) :=
        (M1Body.emb (CohCarrier.GammaH M H)).toAlgebra
      haveI hst : @IsScalarTower ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))
          (instAlgebraIntermediateFieldLaurent (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).toSMul alg.toSMul algQ.toSMul := by
        refine IsScalarTower.of_algebraMap_eq (R := ℚ) (S := ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
          (A := ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) (fun q => ?_)
        apply Subtype.ext
        show ((algebraMap ℚ ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) q :
            ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) q)
        rw [algebraMap_laurentSeries_eq_single, eq_ratCast, SubfieldClass.coe_ratCast, ← HahnSeries.C_apply, coeffEmb, M1Body.coeffMap_C,
          eq_ratCast, map_ratCast]
      haveI hsc : SMulCommClass (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) :=
        ⟨fun a b y => by simp only [Algebra.smul_def]; ring⟩

      have hintc : ∀ a : AlgebraicClosure ℚ, IsIntegral ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
          (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) a) := fun a =>
        ((Algebra.IsIntegral.isIntegral (R := ℚ) a).map (IsScalarTower.toAlgHom ℚ (AlgebraicClosure ℚ)
          ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)))).tower_top
      set B : Subalgebra ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) :=
        Algebra.adjoin ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
          (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)))) with hBdef
      have hBint : ∀ b ∈ B, IsIntegral ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) b := by
        intro b hb
        have hle : B ≤ integralClosure ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) :=
          Algebra.adjoin_le (by rintro _ ⟨a, rfl⟩; exact hintc a)
        exact hle hb
      haveI hBI : Algebra.IsIntegral ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ↥B :=
        ⟨fun b => (isIntegral_algHom_iff B.val Subtype.val_injective).mp (hBint b.1 b.2)⟩
      have hBfield : IsField ↥B := isField_of_isIntegral_of_isField' (Field.toIsField ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
      have hBtop : B = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨z, hz⟩ -
        change z ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) (intFormRatiosC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) at hz
        induction hz using IntermediateField.adjoin_induction with
        | mem w hw =>
          rw [← M1Body.image_intFormRatiosC' (CohCarrier.GammaH M H) (AlgebraicClosure ℚ)] at hw
          obtain ⟨g, hg, rfl⟩ := hw
          have : (⟨coeffEmb (AlgebraicClosure ℚ) g, IntermediateField.subset_adjoin _ _ (by
              rw [← M1Body.image_intFormRatiosC' (CohCarrier.GammaH M H) (AlgebraicClosure ℚ)]; exact ⟨g, hg, rfl⟩)⟩ :
              ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) =
            algebraMap ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) _ ⟨g, intFormRatiosC_subset ℚ _ hg⟩ := rfl
          rw [this]
          exact B.algebraMap_mem _
        | algebraMap a =>
          exact Algebra.subset_adjoin ⟨a, rfl⟩
        | add w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
          have : (⟨w₁ + w₂, IntermediateField.add_mem _ hw₁ hw₂⟩ : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) =
            ⟨w₁, hw₁⟩ + ⟨w₂, hw₂⟩ := rfl
          rw [this]; exact B.add_mem ih₁ ih₂
        | mul w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
          have : (⟨w₁ * w₂, IntermediateField.mul_mem _ hw₁ hw₂⟩ : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) =
            ⟨w₁, hw₁⟩ * ⟨w₂, hw₂⟩ := rfl
          rw [this]; exact B.mul_mem ih₁ ih₂
        | inv w hw ih =>
          by_cases hw0 : w = 0
          · subst hw0
            have : (⟨(0 : LaurentSeries (AlgebraicClosure ℚ))⁻¹, IntermediateField.inv_mem _ hw⟩ :
                ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) = 0 := Subtype.ext (by simp)
            rw [this]; exact B.zero_mem
          · have hb0 : (⟨⟨w, hw⟩, ih⟩ : ↥B) ≠ 0 := fun h => hw0 (by simpa using congrArg (fun t : ↥B => ((t : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) : LaurentSeries (AlgebraicClosure ℚ))) h)
            obtain ⟨c, hc⟩ := hBfield.mul_inv_cancel hb0
            have hc' : ((⟨w, hw⟩ : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) * (c : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)))) = 1 :=
              congrArg Subtype.val hc
            have hinv : (⟨w⁻¹, IntermediateField.inv_mem _ hw⟩ : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) =
                (c : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) := by
              have hne : (⟨w, hw⟩ : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
              have := eq_inv_of_mul_eq_one_right hc'
              rw [this]
              apply Subtype.ext
              simp
            rw [hinv]; exact c.2
      have hgen : Algebra.adjoin ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
          (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)))) = ⊤ := hBtop
      haveI hint : Algebra.IsIntegral ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) :=
        ⟨fun y => hBint y (by rw [hBtop]; exact Algebra.mem_top)⟩

      obtain ⟨jb, hjb, htrb, hfdb⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
        (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) hTΓ
      haveI : PerfectField (AlgebraicClosure ℚ) := IsAlgClosed.perfectField _
      haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) :=
        AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htrb hfdb

      have htr : Transcendental ℚ j := by
        intro halg
        apply ModularCurve.transcendental_jqModC ℚ
        rw [jqModC_rat, ← hj]
        exact halg.algebraMap
      haveI hfd : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :=
        ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CohCarrier.GammaH M H) hTΓ ℚ _
          (M1Body.eq_laurentBaseChange_rat (CohCarrier.GammaH M H)) j (by rw [hj]; ext n; simp [ModularCurve.coeffEmb_coeff])

      have hconst : ∀ y : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), IsAlgebraic ℚ y →
          y ∈ (algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).range :=
        fun y hy => ModularCurve.mem_range_algebraMap_of_isAlgebraic_qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) y hy

      have hreg : KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
          ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))
          (x • KaehlerDifferential.D ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j) ∈
          AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) := by
        set x' : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) := M1Body.emb (CohCarrier.GammaH M H) x with hx'
        set j' : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) := M1Body.emb (CohCarrier.GammaH M H) j with hj'
        have hmap : KaehlerDifferential.map ℚ (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))
            ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))
            (x • KaehlerDifferential.D ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j) =
            x' • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)) j' := by
          rw [LinearMap.map_smul_of_tower, KaehlerDifferential.map_D]
          rfl
        rw [hmap]
        have hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := Gamma1_le_GammaH M H
        refine ModularCurve.smul_D_mem_regularDifferentials_qExpFunctionFieldC_algebraicClosure_of_mul_thetaL_jqModC_eq M
          (CohCarrier.GammaH M H) hΓ₁ f (fun n => PowerSeries.coeff n pf) (fun n => ?_) x' j' ?_ ?_
        ·
          exact (hpf.coeff n).symm
        ·
          rw [hj', M1Body.coe_emb, hj, ← jqModC_rat, coeffEmb]
          exact map_jqModC _
        ·
          have hcq : ∀ y : LaurentSeries ℚ, coeffEmb (AlgebraicClosure ℚ) (qEuler ℚ y) = qEuler (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) y) :=
            fun y => M1Body.coeffMap_qEuler _ y
          have e2 : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
            rw [coeffEmb, ← jqModC_rat]; exact map_jqModC _
          have h1 := congrArg (coeffEmb (AlgebraicClosure ℚ)) hx
          rw [map_mul, hcq, hj, e2, M1Body.coeffEmb_intSeriesC'] at h1
          rw [hx', M1Body.coe_emb, M1Body.thetaL_eq_qEuler', h1, intSeriesC]
          congr 1
          ext n
          simp [PowerSeries.coeff_map, PowerSeries.coeff_mk]

      exact AlgebraicCurve.exists_mem_smul_D_of_map_mem_regularDifferentials_of_constantFieldExtension
        ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H))
        ⟨j, htr, hfd⟩ ⟨jb, htrb, hfdb⟩ hgen hconst _ hreg v

end S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp
end P2MW
export P2MW.S_CuspForm_exists_kaehlerDifferential_diffQExp_eq_ofPowerSeries_and_forall_valuationSubring_of_isIntegralQExp (solution)

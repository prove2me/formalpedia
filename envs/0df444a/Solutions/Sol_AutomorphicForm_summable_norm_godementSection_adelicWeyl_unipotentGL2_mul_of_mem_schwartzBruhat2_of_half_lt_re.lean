-- Prove2me | solution 1 for AutomorphicForm.summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c845852a-7cfa-5977-b2c2-73680c64d210

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Theorems.Thm_AutomorphicForm_summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top
import Theorems.Thm_NumberField_AdelicFourier_exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2
import Theorems.Thm_NumberField_TateGlobal_exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap
import Theorems.Thm_NumberField_TateGlobal_exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdelicFourier_continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell.RankinSelberg

noncomputable section

open NumberField.TateGlobal
open scoped ENNReal NNReal

namespace GodementSum

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem countable_numberField : Countable F :=
  (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance

scoped instance countable_nonzeroVec : Countable {ξ : Fin 2 → F // ξ ≠ 0} := by
  haveI := countable_numberField (F := F)
  infer_instance

def Θ (Φ : (Fin 2 → 𝔸) → ℂ) (g : AdelicGL2 (𝓞 F) F) (t : (𝔸)ˣ) : ℝ :=
  ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
    ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖

theorem Θ_nonneg (Φ : (Fin 2 → 𝔸) → ℂ) (g : AdelicGL2 (𝓞 F) F) (t : (𝔸)ˣ) : 0 ≤ Θ Φ g t :=
  tsum_nonneg fun _ => norm_nonneg _

theorem norm_ideleNorm_cpow (t : (𝔸)ˣ) (w : ℂ) : ‖((ideleNorm F t : ℝ) : ℂ) ^ w‖ = ideleNorm F t ^ w.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos t) w

theorem main
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμu : IsUnitaryChar (𝓞 F) F μ) (hνu : IsUnitaryChar (𝓞 F) F ν)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F)
    (s : ℂ) (hs : 1 / 2 < s.re) (g : AdelicGL2 (𝓞 F) F) :
    Summable fun ξ : F =>
      ‖godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ := by
  set σ : ℝ := s.re with hσ

  have hΦc : Continuous Φ := by
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
    exact (NumberField.AdelicFourier.continuous_integrable_comp_vecMul_mem_and_bottomRowVec_mem_schwartzBruhat_of_mem_schwartzBruhat2 F Φ hΦ).1

  obtain ⟨Ω, hΩm, hΩ⟩ := NumberField.TateGlobal.exists_measurableSet_forall_isFundamentalDomain_range_unitsMap_algebraMap F
  obtain ⟨CK, hCK, hTate⟩ :=
    NumberField.TateGlobal.exists_setIntegral_comp_ideleNorm_eq_mul_integral_Ioi_and_setIntegral_ideleNorm_cpow_eq_div F ν₀
  obtain ⟨-, hrad, -⟩ := hTate Ω (hΩ ν₀)

  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * σ + 1 < N := exists_nat_gt _
  obtain ⟨C, hC0, hC⟩ := (NumberField.AdelicFourier.exists_forall_tsum_norm_apply_smul_vecMul_le_and_continuous_tsum_of_mem_schwartzBruhat2 F hΦ).1
    {g} isCompact_singleton N
  have hsumm : ∀ t : (𝔸)ˣ, Summable fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
      ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖ :=
    fun t => ((hC g (Set.mem_singleton _) t).1).subtype _
  have hΘle : ∀ t : (𝔸)ˣ, Θ Φ g t ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N) :=
    fun t => (hC g (Set.mem_singleton _) t).2

  have hmeasE : Measurable fun t : (𝔸)ˣ => ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      (‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖ₑ) := by
    refine Measurable.ennreal_tsum fun ξ => ?_
    exact ((hΦc.comp (Units.continuous_val.smul continuous_const)).measurable).enorm
  have hΘeq : ∀ t : (𝔸)ˣ, Θ Φ g t = (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      (‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖ₑ)).toReal := by
    intro t
    unfold Θ
    have h1 : (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        (‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖ₑ))
        = ENNReal.ofReal (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
          ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsumm t)]; simp only [ofReal_norm]
    rw [h1, ENNReal.toReal_ofReal (tsum_nonneg fun _ => norm_nonneg _)]
  have hmeasΘ : Measurable (Θ Φ g) := by
    have : Θ Φ g = fun t : (𝔸)ˣ => (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      (‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))‖ₑ)).toReal := funext hΘeq
    rw [this]; exact hmeasE.ennreal_toReal
  have hmeasN : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable

  set R : (𝔸)ˣ → ℝ := fun t => Θ Φ g t * ideleNorm F t ^ (2 * σ + 1) with hR
  have hR0 : ∀ t, 0 ≤ R t := fun t => mul_nonneg (Θ_nonneg _ _ _) (Real.rpow_nonneg (ideleNorm_pos t).le _)
  have hRmeas : Measurable R := hmeasΘ.mul (hmeasN.pow_const _)

  have hw1 : 0 < ((2 * σ - 1 : ℝ) : ℂ).re := by simp; linarith
  obtain ⟨hI1, -, -, -⟩ := hrad ((2 * σ - 1 : ℝ) : ℂ) hw1
  have hint1 : IntegrableOn R (Ω ∩ {t | ideleNorm F t ≤ 1}) ν₀ := by
    refine Integrable.mono' ((hI1.norm).const_mul (2 * C)) hRmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' (hΩm.inter (measurableSet_le hmeasN measurable_const))).2 (Filter.Eventually.of_forall ?_)
    rintro t ⟨-, ht⟩
    have ht1 : ideleNorm F t ≤ 1 := ht
    have hpos := ideleNorm_pos t
    rw [Real.norm_eq_abs, abs_of_nonneg (hR0 t), norm_ideleNorm_cpow, Complex.ofReal_re]
    have hmin : min 1 ((ideleNorm F t)⁻¹ ^ N) ≤ 1 := min_le_left _ _
    have h2 : (1 + (ideleNorm F t)⁻¹ ^ 2) * ideleNorm F t ^ (2 * σ + 1) ≤ 2 * ideleNorm F t ^ (2 * σ - 1) := by
      have e1 : ideleNorm F t ^ (2 * σ + 1) ≤ ideleNorm F t ^ (2 * σ - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hpos ht1 (by linarith)
      have e2 : (ideleNorm F t)⁻¹ ^ 2 * ideleNorm F t ^ (2 * σ + 1) = ideleNorm F t ^ (2 * σ - 1) := by
        rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos]
        norm_num
        congr 1; ring
      nlinarith [e1, e2, Real.rpow_nonneg hpos.le (2 * σ - 1)]
    calc R t = Θ Φ g t * ideleNorm F t ^ (2 * σ + 1) := rfl
      _ ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N) * ideleNorm F t ^ (2 * σ + 1) :=
          mul_le_mul_of_nonneg_right (hΘle t) (Real.rpow_nonneg hpos.le _)
      _ ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * 1 * ideleNorm F t ^ (2 * σ + 1) := by
          gcongr
      _ = C * ((1 + (ideleNorm F t)⁻¹ ^ 2) * ideleNorm F t ^ (2 * σ + 1)) := by ring
      _ ≤ C * (2 * ideleNorm F t ^ (2 * σ - 1)) := mul_le_mul_of_nonneg_left h2 hC0
      _ = 2 * C * ideleNorm F t ^ (2 * σ - 1) := by ring

  have hw2 : 0 < (((N : ℝ) - 2 * σ - 1 : ℝ) : ℂ).re := by simp; linarith
  obtain ⟨-, -, hI2, -⟩ := hrad (((N : ℝ) - 2 * σ - 1 : ℝ) : ℂ) hw2
  have hint2 : IntegrableOn R (Ω ∩ {t | 1 ≤ ideleNorm F t}) ν₀ := by
    refine Integrable.mono' ((hI2.norm).const_mul (2 * C)) hRmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' (hΩm.inter (measurableSet_le measurable_const hmeasN))).2 (Filter.Eventually.of_forall ?_)
    rintro t ⟨-, ht⟩
    have ht1 : 1 ≤ ideleNorm F t := ht
    have hpos := ideleNorm_pos t
    rw [Real.norm_eq_abs, abs_of_nonneg (hR0 t), norm_ideleNorm_cpow, Complex.neg_re, Complex.ofReal_re]
    have hinvle : (ideleNorm F t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
    have hinv0 : 0 ≤ (ideleNorm F t)⁻¹ := inv_nonneg.2 hpos.le
    have hmin : min 1 ((ideleNorm F t)⁻¹ ^ N) ≤ (ideleNorm F t)⁻¹ ^ N := min_le_right _ _
    have hsq : (ideleNorm F t)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hinv0 hinvle
    have e2 : (ideleNorm F t)⁻¹ ^ N * ideleNorm F t ^ (2 * σ + 1) = ideleNorm F t ^ (-((N : ℝ) - 2 * σ - 1)) := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos]
      congr 1; ring
    calc R t = Θ Φ g t * ideleNorm F t ^ (2 * σ + 1) := rfl
      _ ≤ C * (1 + (ideleNorm F t)⁻¹ ^ 2) * min 1 ((ideleNorm F t)⁻¹ ^ N) * ideleNorm F t ^ (2 * σ + 1) :=
          mul_le_mul_of_nonneg_right (hΘle t) (Real.rpow_nonneg hpos.le _)
      _ ≤ C * (1 + 1) * (ideleNorm F t)⁻¹ ^ N * ideleNorm F t ^ (2 * σ + 1) := by
          gcongr
      _ = 2 * C * ((ideleNorm F t)⁻¹ ^ N * ideleNorm F t ^ (2 * σ + 1)) := by ring
      _ = 2 * C * ideleNorm F t ^ (-((N : ℝ) - 2 * σ - 1)) := by rw [e2]

  have hcover : Ω = (Ω ∩ {t | ideleNorm F t ≤ 1}) ∪ (Ω ∩ {t | 1 ≤ ideleNorm F t}) := by
    ext t; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro ht; rcases le_total (ideleNorm F t) 1 with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, h⟩
    · rintro (⟨ht, -⟩ | ⟨ht, -⟩) <;> exact ht
  have hintΩ : IntegrableOn R Ω ν₀ := by rw [hcover]; exact hint1.union hint2

  have hre : (2 * s + 1).re = 2 * σ + 1 := by rw [hσ]; simp [Complex.add_re, Complex.mul_re]
  have habs : ∫⁻ t in Ω, ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))
        * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ ∂ν₀ < ⊤ := by
    have hpt : ∀ t : (𝔸)ˣ, (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Φ ((t : 𝔸) • Matrix.vecMul (fun i => algebraMap F 𝔸 (ξ.1 i)) (g : Matrix (Fin 2) (Fin 2) 𝔸))
          * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ) = ‖R t‖ₑ := by
      intro t
      have hχ : ‖(((μ * ν⁻¹) t : ℂˣ) : ℂ)‖ = 1 := by
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv,
          hμu t, hνu t, inv_one, mul_one]
      have hfac : ∀ x : Fin 2 → 𝔸, ‖Φ x * (((μ * ν⁻¹) t : ℂˣ) : ℂ) * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)‖ₑ
          = ENNReal.ofReal (‖Φ x‖ * ideleNorm F t ^ (2 * σ + 1)) := by
        intro x
        rw [← ofReal_norm, norm_mul, norm_mul, hχ, mul_one, norm_ideleNorm_cpow, hre]
      simp_rw [hfac]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun ξ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ideleNorm_pos t).le _))
        ((hsumm t).mul_right _), tsum_mul_right, Real.enorm_eq_ofReal (hR0 t)]
      rfl
    simp_rw [hpt]
    exact hintΩ.2
  exact (AutomorphicForm.summable_norm_godementSection_bruhat_and_norm_add_tsum_norm_le_mul_setIntegral_tsum_norm_of_lintegral_tsum_enorm_lt_top
    F ν₀ Ω (hΩ ν₀) μ ν hμu hνu (moduleChar F) (moduleChar_pos F) Φ hΦc s g habs).1

end GodementSum
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re.GodementSum"

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsIdeleClassChar (𝓞 F) F μ) (hν : IsIdeleClassChar (𝓞 F) F ν)
    (hμu : IsUnitaryChar (𝓞 F) F μ) (hνu : IsUnitaryChar (𝓞 F) F ν)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ schwartzBruhat2 F)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
      ‖godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ := fun g =>
  GodementSum.main ν₀ μ ν hμu hνu Φ hΦ s hs g

end
end S_AutomorphicForm_summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re
end P2MW
export P2MW.S_AutomorphicForm_summable_norm_godementSection_adelicWeyl_unipotentGL2_mul_of_mem_schwartzBruhat2_of_half_lt_re (solution)

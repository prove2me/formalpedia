-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrk_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:55.915403+00:00
-- url     : https://prove2.me/submissions/0dea4985-64fa-44dd-9195-556d4b080fa7

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkAesmTsum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrkaMeasKabRight
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_K_symm
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_K_smul
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_meas_Kab_right
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_lint
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrka_summable_of
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_isFD
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrk_aesm_tsum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} [Countable Γ] {D : Set G} {φ : G → ℂ}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (h : rr_FD μ Γ D) (hφm : Measurable φ)
    (hsa : ∀ z, φ z⁻¹ = star (φ z)) (hid : ∀ z, ∫ g, φ g * φ (g⁻¹ * z) ∂μ = φ z) (x : G)
    (hx : ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ ≠ ∞) :
    Summable (fun γ : Γ => φ (x⁻¹ * (γ : G) * x)) ∧
      rrk_K Γ φ x x = ((∫ y in D, ‖rrk_K Γ φ x y‖ ^ 2 ∂μ : ℝ) : ℂ) ∧
      MemLp (fun y => rrk_K Γ φ x y) 2 (μ.restrict D) := by
  set ψ : Γ → G → ℂ := fun γ y => φ (x⁻¹ * y) * φ (y⁻¹ * (γ : G) * x) with hψ
  have hψm : ∀ γ, Measurable (ψ γ) := fun γ =>
    (hφm.comp (measurable_const_mul _)).mul (hφm.comp ((measurable_inv.mul_const _).mul_const _))
  have hψint : ∀ γ : Γ, ∫ y, ψ γ y ∂μ = φ (x⁻¹ * (γ : G) * x) := by
    intro γ
    rw [← hid (x⁻¹ * (γ : G) * x),
      ← integral_mul_left_eq_self (fun g => φ g * φ (g⁻¹ * (x⁻¹ * (γ : G) * x))) x⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e : (x⁻¹ * y)⁻¹ * (x⁻¹ * (γ : G) * x) = y⁻¹ * (γ : G) * x := by simp [mul_assoc]
    simp only [hψ, e]
  have hpt : ∀ y, ∑' γ : Γ, ‖ψ γ y‖ₑ = ‖φ (x⁻¹ * y)‖ₑ * rrk_Kab Γ φ y x := by
    intro y
    simp only [hψ, enorm_mul]
    rw [ENNReal.tsum_mul_left]
    rfl
  have hsum : ∑' γ : Γ, ∫⁻ y, ‖ψ γ y‖ₑ ∂μ = ∫⁻ y in D, (rrk_Kab Γ φ x y) ^ 2 ∂μ := by
    rw [← rrka_lint h hφm hsa x, ← lintegral_tsum (fun γ => (hψm γ).enorm.aemeasurable)]
    exact lintegral_congr hpt
  have hfin : ∑' γ : Γ, ∫⁻ y, ‖ψ γ y‖ₑ ∂μ ≠ ∞ := by rw [hsum]; exact hx
  have hS : Summable (fun γ : Γ => φ (x⁻¹ * (γ : G) * x)) := by
    refine rrka_summable_of (ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum fun γ => ?_))
    rw [← hψint γ]
    exact enorm_integral_le_lintegral_enorm _
  set Ψ : G → ℂ := fun y => φ (x⁻¹ * y) * rrk_K Γ φ y x with hΨ
  have hΨeq : Ψ = fun y => ∑' γ : Γ, ψ γ y := by
    funext y
    simp only [hΨ, hψ]
    rw [tsum_mul_left]
    rfl
  have hfin2 : ∫⁻ y, ∑' γ : Γ, ‖ψ γ y‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum (fun γ => (hψm γ).enorm.aemeasurable)]; exact hfin
  have hae : ∀ᵐ y ∂μ, Summable fun γ : Γ => ψ γ y := by
    filter_upwards [ae_lt_top (Measurable.tsum fun γ => (hψm γ).enorm) hfin2] with y hy
    exact rrka_summable_of hy.ne
  have hΨm : AEStronglyMeasurable Ψ μ := by
    rw [hΨeq]; exact rrk_aesm_tsum (fun γ => (hψm γ).aestronglyMeasurable) hae
  have hΨfin : ∫⁻ y, ‖Ψ y‖ₑ ∂μ < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (lt_top_iff_ne_top.2 hfin2)
    rw [hΨeq]
    exact enorm_tsum_le_tsum_enorm
  have hΨint : Integrable Ψ μ := ⟨hΨm, hasFiniteIntegral_iff_enorm.2 hΨfin⟩
  have e1 : rrk_K Γ φ x x = ∫ y, Ψ y ∂μ := by
    calc rrk_K Γ φ x x = ∑' γ : Γ, ∫ y, ψ γ y ∂μ := tsum_congr fun γ => (hψint γ).symm
      _ = ∫ y, ∑' γ : Γ, ψ γ y ∂μ := (integral_tsum (fun γ => (hψm γ).aestronglyMeasurable) hfin).symm
      _ = ∫ y, Ψ y ∂μ := by rw [hΨeq]
  have e2 := (rr_isFD h).integral_eq_tsum'' Ψ hΨint
  have e3 : ∑' δ : Γ, ∫ y in D, Ψ (δ • y) ∂μ = ∫ y in D, ∑' δ : Γ, Ψ (δ • y) ∂μ := by
    refine (integral_tsum (μ := μ.restrict D) (f := fun (δ : Γ) y => Ψ (δ • y)) (fun δ => ?_) ?_).symm
    · exact (hΨm.comp_measurePreserving (measurePreserving_smul δ μ)).restrict
    · rw [← (rr_isFD h).lintegral_eq_tsum'' (fun y => ‖Ψ y‖ₑ)]
      exact hΨfin.ne
  have e4 : ∀ y, ∑' δ : Γ, Ψ (δ • y) = ((‖rrk_K Γ φ x y‖ ^ 2 : ℝ) : ℂ) := by
    intro y
    have a : ∀ δ : Γ, Ψ (δ • y) = φ (x⁻¹ * (δ : G) * y) * rrk_K Γ φ y x := by
      intro δ
      simp only [hΨ]
      rw [Subgroup.smul_def, smul_eq_mul, rrka_K_smul, ← mul_assoc]
    rw [tsum_congr a, tsum_mul_right, rrka_K_symm hsa x y]
    show rrk_K Γ φ x y * star (rrk_K Γ φ x y) = _
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have haeD : ∀ᵐ y ∂μ.restrict D, rrk_Kab Γ φ x y < ∞ := by
    filter_upwards [ae_lt_top ((rrka_meas_Kab_right (Γ := Γ) hφm x).pow_const 2) hx] with y hy
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at hy
    simp at hy
  have hKm : AEStronglyMeasurable (fun y => rrk_K Γ φ x y) (μ.restrict D) := by
    refine rrk_aesm_tsum (fun γ => (hφm.comp (measurable_const_mul _)).aestronglyMeasurable) ?_
    filter_upwards [haeD] with y hy
    exact rrka_summable_of hy.ne
  refine ⟨hS, ?_, hKm, ?_⟩
  · rw [e1, e2, e3, ← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall e4)
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (lt_top_iff_ne_top.2 hx)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    gcongr
    exact enorm_tsum_le_tsum_enorm
end Formalism.MainNotions.LeviCoordinates

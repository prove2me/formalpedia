-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:24.008912+00:00
-- url     : https://prove2.me/submissions/aa1c8bf1-6cf4-49dd-bd69-09e326bc59ab

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_rhoXY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_MXY_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_sm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_remainder_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_cof_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_z_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_Tpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_cof_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution (m : ℕ) (Kc : Set ℂ) (hK : IsCompact Kc) (h0 : (0 : ℂ) ∉ Kc) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) :
    ∃ t₁ c Rz : ℝ, 0 < t₁ ∧ t₁ ≤ 1 ∧ 0 < c ∧ 1 ≤ Rz ∧ ∀ D ∈ Kc, ∀ z : ℂ, z ^ (m + 2) = (-1) ^ (m + 3) * D →
      ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ t₁ →
      z ≠ 0 ∧ ‖z‖ ≤ Rz ∧ ‖D‖ ≤ Rz ∧ c ≤ ‖z‖ ^ (m + 1) ∧
      (∀ (y : UT (m + 2) → ℂ) (τ' : ℂ), ‖y‖ ≤ 2 * ‖t‖ ^ (-ε) → ‖τ'‖ ≤ ‖t‖ →
        c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖) ∧
      (∀ y : UT (m + 2) → ℂ, ‖y‖ ≤ ‖t‖ ^ (-ε) → ‖MXY m D t (fun _ => z, y)‖ ≤ ‖t‖ ^ (-ε)) := by
  obtain ⟨RD, hRD⟩ := hK.isBounded.exists_norm_le
  obtain ⟨rD, hrD0, hrD⟩ : ∃ r : ℝ, 0 < r ∧ ∀ D ∈ Kc, r ≤ ‖D‖ := by
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
    refine ⟨r, hr, fun D hD => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hb (by simpa using hlt) hD
  set Rz : ℝ := max 1 RD with hRz
  set rz : ℝ := min 1 rD with hrz
  have hRz1 : 1 ≤ Rz := le_max_left _ _
  have hrz0 : 0 < rz := lt_min one_pos hrD0
  set c : ℝ := rz ^ (m + 1) with hc
  have hc0 : 0 < c := pow_pos hrz0 _
  set C₁ : ℝ := ((m : ℝ) + 1) ^ (m + 1) * (2 * Rz) ^ m with hC₁
  set C₂ : ℝ := ((m : ℝ) + 1) ^ (m + 2) * (2 * Rz) ^ (m + 1) with hC₂
  have hC₁0 : 0 < C₁ := by positivity
  have hC₂0 : 0 < C₂ := by positivity
  set Rb : ℝ := max ((2 * Rz + Rz + C₂) * (2 / c)) Rz with hRb
  have hRb1 : 1 ≤ Rb := hRz1.trans (le_max_right _ _)
  have hRb0 : 0 < Rb := by linarith
  refine ⟨min 1 (min ((c / (2 * C₁)) ^ 2) (Rb ^ (-(1 / ε)))), c, Rz, ?_, min_le_left _ _, hc0, hRz1, ?_⟩
  · refine lt_min one_pos (lt_min (by positivity) (Real.rpow_pos_of_pos hRb0 _))
  intro D hD z hzD t ht htle
  have ht0 : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have ht1 : ‖t‖ ≤ 1 := htle.trans (min_le_left _ _)
  have ht2 : ‖t‖ ≤ (c / (2 * C₁)) ^ 2 := htle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : ‖t‖ ≤ Rb ^ (-(1 / ε)) := htle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnz : ‖z‖ ^ (m + 2) = ‖D‖ := by
    rw [← norm_pow, hzD, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  obtain ⟨hzl, hzu⟩ := z_bounds m hnz (hrD D hD) (hRD D hD)
  have hz0 : z ≠ 0 := by
    rw [← norm_pos_iff]
    exact lt_of_lt_of_le hrz0 hzl
  have hcz : c ≤ ‖z‖ ^ (m + 1) := pow_le_pow_left₀ hrz0.le hzl _
  set T : ℝ := ‖t‖ ^ (-ε) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hsq : Real.sqrt ‖t‖ ≤ c / (2 * C₁) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ c / (2 * C₁))]
    exact Real.sqrt_le_sqrt ht2
  have hsq1 : Real.sqrt ‖t‖ ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ht1
  have hRbT : Rb ≤ T := by
    have h1 : (Rb ^ (-(1 / ε))) ^ (-ε) ≤ T := Real.rpow_le_rpow_of_nonpos ht0 ht3 (by linarith)
    rw [← Real.rpow_mul hRb0.le] at h1
    have h2 : -(1 / ε) * -ε = 1 := by field_simp
    rwa [h2, Real.rpow_one] at h1
  have hR1 : 1 ≤ 2 * Rz * T := by nlinarith
  have hzR : ‖z‖ ≤ 2 * Rz * T := by nlinarith
  have hcof : ∀ (y : UT (m + 2) → ℂ) (τ' : ℂ), ‖y‖ ≤ 2 * T → ‖τ'‖ ≤ ‖t‖ →
      c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖ := by
    intro y τ' hy hτ'
    refine cof_lower m z τ' y hR1 (hτ'.trans ht1) hzR (by nlinarith) hcz ?_
    calc ‖τ'‖ * (((m : ℝ) + 1) ^ (m + 1) * (2 * Rz * T) ^ m)
        ≤ ‖t‖ * (((m : ℝ) + 1) ^ (m + 1) * (2 * Rz * T) ^ m) :=
          mul_le_mul_of_nonneg_right hτ' (by positivity)
      _ = C₁ * (T ^ m * ‖t‖) := by rw [hC₁, mul_pow]; ring
      _ ≤ C₁ * Real.sqrt ‖t‖ :=
          mul_le_mul_of_nonneg_left (Tpow m ht0 ht1 hε0 hε (by omega)) hC₁0.le
      _ ≤ C₁ * (c / (2 * C₁)) := mul_le_mul_of_nonneg_left hsq hC₁0.le
      _ = c / 2 := by field_simp
  refine ⟨hz0, hzu, (hRD D hD).trans (le_max_right _ _), hcz, hcof, ?_⟩
  intro y hy
  have hyR : ‖y‖ ≤ 2 * Rz * T := by nlinarith
  have hcl := hcof y t (by linarith) le_rfl
  have hρ : ‖rhoXY m D t (fun _ => z, y)‖ ≤ (2 * Rz + Rz + C₂) * (2 / c) := by
    rw [rhoXY_eq, norm_mul, norm_inv]
    have e1 : ‖cofXY m t (fun _ => z, y)‖⁻¹ ≤ 2 / c := by
      rw [inv_le_comm₀ (by linarith) (by positivity)]
      rw [inv_div]
      exact hcl
    have e2 : ‖t ^ (m + 1) * sm m (fun _ => z, y)‖ ≤ 2 * Rz := by
      rw [norm_mul, norm_pow]
      have a1 : ‖sm m (fun _ => z, y)‖ ≤ 2 * Rz * T :=
        sm_le m (fun _ => z, y) (by linarith) (fun _ => hzR) hyR
      have a2 : ‖t‖ ^ (m + 1) ≤ ‖t‖ := pow_le_of_le_one ht0.le ht1 (by omega)
      calc ‖t‖ ^ (m + 1) * ‖sm m (fun _ => z, y)‖ ≤ ‖t‖ * (2 * Rz * T) :=
            mul_le_mul a2 a1 (norm_nonneg _) ht0.le
        _ = 2 * Rz * (T ^ 1 * ‖t‖) := by ring
        _ ≤ 2 * Rz * Real.sqrt ‖t‖ :=
            mul_le_mul_of_nonneg_left (Tpow m ht0 ht1 hε0 hε (by omega)) (by positivity)
        _ ≤ 2 * Rz * 1 := mul_le_mul_of_nonneg_left hsq1 (by positivity)
        _ = 2 * Rz := by ring
    have e3 : ‖t * r1XY m t (fun _ => z, y)‖ ≤ C₂ := by
      rw [norm_mul]
      have a1 := remainder_norm_le m t (fun _ => z, y) hR1 ht1 (fun _ => hzR) hyR
      calc ‖t‖ * ‖r1XY m t (fun _ => z, y)‖ ≤ ‖t‖ * (((m : ℝ) + 1) ^ (m + 2) * (2 * Rz * T) ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left a1 ht0.le
        _ = C₂ * (T ^ (m + 1) * ‖t‖) := by rw [hC₂, mul_pow]; ring
        _ ≤ C₂ * Real.sqrt ‖t‖ :=
            mul_le_mul_of_nonneg_left (Tpow m ht0 ht1 hε0 hε (by omega)) hC₂0.le
        _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left hsq1 hC₂0.le
        _ = C₂ := by ring
    have e4 : ‖t ^ (m + 1) * sm m (fun _ => z, y) - D - t * r1XY m t (fun _ => z, y)‖ ≤ 2 * Rz + Rz + C₂ := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add e2 ?_)) e3)
      exact (hRD D hD).trans (le_max_right _ _)
    exact mul_le_mul e4 e1 (by positivity) (by positivity)
  refine MXY_le m D t (fun _ => z, y) (by linarith) (ht1.trans hT1) ?_ (fun _ => ?_) hy
  · exact hρ.trans ((le_max_left _ _).trans hRbT)
  · exact hzu.trans ((le_max_right _ _).trans hRbT)
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim

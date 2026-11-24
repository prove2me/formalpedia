-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.choice_of_constants
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:28.599074+00:00
-- url     : https://prove2.me/submissions/3790f942-d71f-45e4-8316-136a81593178

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_LevelGrowthBounds_half_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real Formalism.FourierDecayAlt.P.LevelGrowthBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ChoiceOfConstants := by
  intro C₁ CE C' C Θ Kx f r hC₁ hCE hf hK hC' hC hΘ' hΘ hr
  have hΘ0 : 0 < Θ := by linarith
  have hf0 : f ≠ 0 := by omega

  have hd0 : 0 ≤ C₁ / Θ := by positivity
  have hc0 : 0 ≤ CE / Θ := by positivity
  have hu0 : 0 ≤ (C₁ + CE) / Θ := by positivity
  have hu8 : (C₁ + CE) / Θ ≤ 1 / 8 := by
    rw [div_le_iff₀ hΘ0]; linarith
  have hdu : C₁ / Θ ≤ (C₁ + CE) / Θ := by
    apply div_le_div_of_nonneg_right _ hΘ0.le; linarith
  have hcu : CE / Θ ≤ (C₁ + CE) / Θ := by
    apply div_le_div_of_nonneg_right _ hΘ0.le; linarith
  have hrp : Θ ^ (-(Kx - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ (by linarith)
  have hrp0 : 0 ≤ Θ ^ (-(Kx - 5 / 2)) := Real.rpow_nonneg hΘ0.le _
  have he0 : 0 ≤ CE * Θ ^ (-(Kx - 5 / 2)) := mul_nonneg hCE.le hrp0
  have hec : CE * Θ ^ (-(Kx - 5 / 2)) ≤ CE / Θ := by
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hrp hCE.le

  have p1 : (C₁ / Θ) ^ f ≤ (1 / 8 : ℝ) ^ f := pow_le_pow_left₀ hd0 (hdu.trans hu8) f
  have p8 : (1 / 8 : ℝ) ^ f ≤ 1 / 8 := by
    have := pow_le_pow_of_le_one (show (0:ℝ) ≤ 1 / 8 by norm_num) (by norm_num) hf
    simpa using this
  have p3 : (CE * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (CE / Θ) ^ f := pow_le_pow_left₀ he0 hec f
  have pdu : (C₁ / Θ) ^ f ≤ ((C₁ + CE) / Θ) ^ f := pow_le_pow_left₀ hd0 hdu f
  have pcu : (CE / Θ) ^ f ≤ ((C₁ + CE) / Θ) ^ f := pow_le_pow_left₀ hc0 hcu f
  have pu8 : ((C₁ + CE) / Θ) ^ f ≤ 1 / 8 := (pow_le_pow_left₀ hu0 hu8 f).trans p8
  have pu0 : 0 ≤ ((C₁ + CE) / Θ) ^ f := pow_nonneg hu0 f
  have p4 : (CE * Θ ^ (-(Kx - 5 / 2))) ^ f + 2 * (C₁ / Θ) ^ f ≤ 3 * ((C₁ + CE) / Θ) ^ f := by
    linarith

  have h12 : 12 * ((C₁ + CE) / Θ) ^ f ≤ (C / Θ) ^ f := by
    have a1 : (12:ℝ) ≤ 12 ^ f := by
      have := pow_le_pow_right₀ (show (1:ℝ) ≤ 12 by norm_num) hf
      simpa using this
    have a2 : (12 * ((C₁ + CE) / Θ)) ^ f ≤ (C / Θ) ^ f := by
      apply pow_le_pow_left₀ (by positivity)
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hC hΘ0.le
    rw [mul_pow] at a2
    nlinarith [mul_le_mul_of_nonneg_right a1 pu0]
  have hr12 : (r:ℝ) * (12 * ((C₁ + CE) / Θ) ^ f) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h12 (Nat.cast_nonneg r)).trans hr
  have hh := half_bound r _ pu0 pu8 hr12
  refine ⟨p1, p1.trans p8, p3, p4, ?_⟩
  have hr1 : (0:ℝ) ≤ (r:ℝ) + 1 := by positivity
  exact (mul_le_mul_of_nonneg_left p4 hr1).trans hh
end Formalism.FourierDecayAlt.P

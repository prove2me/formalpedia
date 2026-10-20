-- Prove2me | solution 2 for CohnElkies.saddleSourceSecondBranch_outerMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:05:58.914813+00:00
-- url     : https://prove2.me/submissions/f83f85c5-ecca-4577-9aca-00cda114ad99

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {ℓ δ : ℝ} (hℓ : 1 ≤ ℓ) (hδ : 0 ≤ δ) :
    2 * max (1 : ℝ)
        ((Real.sqrt
          (saddleSourceSecondBranchGammaGaussianRate
            ℓ δ / 6) ^ 3)⁻¹) *
          Real.sqrt
            (Real.pi /
              (saddleSourceSecondBranchGammaGaussianRate
                ℓ δ / 2)) +
      2 * max (1 : ℝ)
        (((saddleSourceSecondBranchGammaLinearRate
          ℓ / 6) ^ 3)⁻¹) *
          (2 /
            (saddleSourceSecondBranchGammaLinearRate
              ℓ / 2)) ≤
        saddleSourceSecondBranchMomentCoefficient *
          (2 + δ) ^ 4 := by
  have hC : (16 : ℝ) ≤ 8 * Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have ht : (2 : ℝ) ≤ 2 + δ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hpi := Real.pi_pos
  have hG : saddleSourceSecondBranchGammaGaussianRate ℓ δ = ℓ / ((8 * Real.exp 1) * (2 + δ)) := by
    unfold saddleSourceSecondBranchGammaGaussianRate; rw [div_div]
  have hL : saddleSourceSecondBranchGammaLinearRate ℓ = ℓ / (8 * Real.exp 1) := rfl
  simp only [saddleSourceSecondBranchMomentCoefficient]
  rw [hG, hL]
  generalize 8 * Real.exp 1 = C at hC ⊢
  generalize 2 + δ = t at ht ⊢
  have hCt : 0 < C * t := by positivity
  -- term 1 pieces
  have hy : (Real.sqrt (ℓ / (C * t) / 6))⁻¹ ≤ 6 * C * t := by
    have hsq : 0 < Real.sqrt (ℓ / (C * t) / 6) := Real.sqrt_pos.mpr (by positivity)
    rw [inv_le_comm₀ hsq (by positivity), Real.le_sqrt (by positivity) (by positivity)]
    rw [div_div, inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    rw [show ℓ / (C * t * 6) * (6 * C * t) ^ 2 = 6 * C * t * ℓ by field_simp]
    nlinarith
  have hmax1 : max (1 : ℝ) ((Real.sqrt (ℓ / (C * t) / 6) ^ 3)⁻¹) ≤ (1 + (6 * C) ^ 3) * t ^ 3 := by
    have ht3 : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ (by linarith)
    apply max_le
    · nlinarith [pow_pos (show (0:ℝ) < 6 * C by positivity) 3]
    · rw [← inv_pow]
      calc ((Real.sqrt (ℓ / (C * t) / 6))⁻¹) ^ 3 ≤ (6 * C * t) ^ 3 :=
            pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hy 3
        _ = (6 * C) ^ 3 * t ^ 3 := by ring
        _ ≤ (1 + (6 * C) ^ 3) * t ^ 3 := by nlinarith
  have hs : Real.sqrt (Real.pi / (ℓ / (C * t) / 2)) ≤ (1 + 2 * Real.pi * C) * t := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [show Real.pi / (ℓ / (C * t) / 2) = 2 * Real.pi * C * t / ℓ by field_simp]
    calc 2 * Real.pi * C * t / ℓ ≤ 2 * Real.pi * C * t := div_le_self (by positivity) hℓ
      _ ≤ ((1 + 2 * Real.pi * C) * t) ^ 2 := by
        have h1 : 0 ≤ 2 * Real.pi * C := by positivity
        nlinarith [mul_nonneg h1 h1, mul_nonneg h1 (show (0:ℝ) ≤ t by linarith)]
  -- term 2 pieces
  have hmax2 : max (1 : ℝ) (((ℓ / C / 6) ^ 3)⁻¹) ≤ 1 + (6 * C) ^ 3 := by
    apply max_le
    · nlinarith [pow_pos (show (0:ℝ) < 6 * C by positivity) 3]
    · rw [← inv_pow]
      have : (ℓ / C / 6)⁻¹ ≤ 6 * C := by
        rw [inv_div, div_div_eq_mul_div, div_le_iff₀ hℓ0]; nlinarith
      have := pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) this 3
      linarith
  have hlin : 2 / (ℓ / C / 2) ≤ 4 * C := by
    rw [show 2 / (ℓ / C / 2) = 4 * C / ℓ by field_simp; ring]
    exact div_le_self (by positivity) hℓ
  have ht4 : (1 : ℝ) ≤ t ^ 4 := one_le_pow₀ (by linarith)
  have hA : 0 ≤ 1 + (6 * C) ^ 3 := by positivity
  have hm1 : 0 ≤ max (1 : ℝ) ((Real.sqrt (ℓ / (C * t) / 6) ^ 3)⁻¹) := le_trans zero_le_one (le_max_left _ _)
  have hm2 : 0 ≤ max (1 : ℝ) (((ℓ / C / 6) ^ 3)⁻¹) := le_trans zero_le_one (le_max_left _ _)
  have e1 : 2 * max (1 : ℝ) ((Real.sqrt (ℓ / (C * t) / 6) ^ 3)⁻¹) *
      Real.sqrt (Real.pi / (ℓ / (C * t) / 2)) ≤
      2 * (1 + (6 * C) ^ 3) * (1 + 2 * Real.pi * C) * t ^ 4 := by
    calc _ ≤ 2 * ((1 + (6 * C) ^ 3) * t ^ 3) * ((1 + 2 * Real.pi * C) * t) := by
          gcongr
      _ = _ := by ring
  have e2 : 2 * max (1 : ℝ) (((ℓ / C / 6) ^ 3)⁻¹) * (2 / (ℓ / C / 2)) ≤
      8 * C * (1 + (6 * C) ^ 3) * t ^ 4 := by
    calc _ ≤ 2 * (1 + (6 * C) ^ 3) * (4 * C) := by gcongr
      _ = 8 * C * (1 + (6 * C) ^ 3) * 1 := by ring
      _ ≤ 8 * C * (1 + (6 * C) ^ 3) * t ^ 4 := by gcongr
  nlinarith [e1, e2]


-- Prove2me | solution 2 for CohnElkies.stripPoissonKernel_le_mass_mul_exponential
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:13.342527+00:00
-- url     : https://prove2.me/submissions/b94722ee-2dfd-4a2c-b391-1701814b7492

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology


theorem solution
    {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1)
    (T : ℝ) :
    stripPoissonKernel σ T ≤
      stripBottomMass σ * stripPoissonExponentialMajorant T := by
  unfold stripPoissonKernel stripBottomMass stripPoissonExponentialMajorant stripAngle
  have hpi := Real.pi_pos
  have hc : Real.cos (Real.pi * (1 + σ) / 2) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith) (by nlinarith)
  have hs : 0 ≤ Real.sin (Real.pi * (1 + σ) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
  have hsθ : Real.sin (Real.pi * (1 + σ) / 2) ≤ Real.pi * (1 - σ) / 2 := by
    have : Real.sin (Real.pi * (1 + σ) / 2) = Real.sin (Real.pi * (1 - σ) / 2) := by
      rw [← Real.sin_pi_sub]; congr 1; ring
    rw [this]; exact Real.sin_le (by nlinarith)
  have hch : Real.exp (Real.pi / 2 * |T|) / 2 ≤ Real.cosh (Real.pi * T / 2) := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have : |Real.pi * T / 2| = Real.pi / 2 * |T| := by
      rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num; ring
    rw [this]
    linarith [Real.exp_pos (-(Real.pi / 2 * |T|))]
  have hG := Real.exp_pos (Real.pi / 2 * |T|)
  have hFG : Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hD : 0 < 4 * (Real.cosh (Real.pi * T / 2) - Real.cos (Real.pi * (1 + σ) / 2)) := by
    nlinarith
  rw [div_le_iff₀ hD]
  have hF := Real.exp_pos (-(Real.pi / 2) * |T|)
  have h1σ : 0 ≤ 1 - σ := by linarith
  have key : (1 - σ) / 2 * (Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|)) *
      (4 * (Real.exp (Real.pi / 2 * |T|) / 2)) = Real.pi * (1 - σ) / 2 := by
    have : (1 - σ) / 2 * (Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|)) *
      (4 * (Real.exp (Real.pi / 2 * |T|) / 2)) =
        (1 - σ) / 2 * (Real.pi / 2) * 2 * (Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|)) := by ring
    rw [this, hFG]; ring
  have hR : 0 ≤ (1 - σ) / 2 * (Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|)) := by positivity
  have hmono : 4 * (Real.exp (Real.pi / 2 * |T|) / 2) ≤
      4 * (Real.cosh (Real.pi * T / 2) - Real.cos (Real.pi * (1 + σ) / 2)) := by linarith
  calc Real.sin (Real.pi * (1 + σ) / 2) ≤ Real.pi * (1 - σ) / 2 := hsθ
    _ = _ := key.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono hR


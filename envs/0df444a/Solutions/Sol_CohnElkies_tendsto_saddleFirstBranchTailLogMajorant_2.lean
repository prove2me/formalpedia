-- Prove2me | solution 2 for CohnElkies.tendsto_saddleFirstBranchTailLogMajorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:46:34.201596+00:00
-- url     : https://prove2.me/submissions/561017df-7eb6-4657-8577-aae1a604fc44

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology


theorem solution
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    Tendsto (saddleFirstBranchTailLogMajorant c C)
      atTop (𝓝 (0 : ℝ)) := by
  have hL : Tendsto (fun ℓ : ℝ => Real.log ℓ / 4) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num)
  have hR : Tendsto (fun ℓ : ℝ => (Real.log ℓ / 4) ^ (1 / 6 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hL
  have hk : -(c / (4 * C)) < 0 := by have : 0 < c / (4 * C) := by positivity
                                     linarith
  have hE : Tendsto (fun ℓ : ℝ => Real.exp (-(c / (4 * C)) * (Real.log ℓ / 4) ^ (1 / 6 : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hR.const_mul_atTop_of_neg hk)
  have hS0 : Tendsto (fun ℓ : ℝ => C / (Real.log ℓ / 4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have hS : Tendsto (fun ℓ : ℝ => Real.sqrt (C / (Real.log ℓ / 4))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hS0
    rwa [Real.sqrt_zero] at this
  have h := (hE.const_mul (4 * Real.sqrt (Real.pi * C / c))).add (hS.const_mul (16 / c))
  simp only [mul_zero, add_zero] at h
  exact h


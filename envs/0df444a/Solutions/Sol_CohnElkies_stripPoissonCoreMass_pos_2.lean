-- Prove2me | solution 2 for CohnElkies.stripPoissonCoreMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:15:58.14147+00:00
-- url     : https://prove2.me/submissions/f76e122a-709e-4f25-af56-18b88acf9d90

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
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    0 < stripPoissonCoreMass σ := by
  unfold stripPoissonCoreMass
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hθ0 : 0 < stripAngle σ := by unfold stripAngle; have := Real.pi_pos; nlinarith
  have hθπ : stripAngle σ < Real.pi := by unfold stripAngle; have := Real.pi_pos; nlinarith
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hcos : Real.cos (stripAngle σ) < 1 := by nlinarith [Real.sin_sq_add_cos_sq (stripAngle σ), Real.cos_le_one (stripAngle σ)]
  have hden : ∀ T : ℝ, 0 < 4 * (Real.cosh (Real.pi * T / 2) - Real.cos (stripAngle σ)) := fun T => by
    have := Real.one_le_cosh (Real.pi * T / 2); linarith
  have hcont : Continuous (stripPoissonKernel σ) := by
    unfold stripPoissonKernel
    exact continuous_const.div (by fun_prop) (fun T => (hden T).ne')
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
  · intro T _
    unfold stripPoissonKernel
    exact div_pos hsin (hden T)
  · norm_num


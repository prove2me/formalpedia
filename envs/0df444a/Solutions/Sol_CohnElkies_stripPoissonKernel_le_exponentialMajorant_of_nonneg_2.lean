-- Prove2me | solution 2 for CohnElkies.stripPoissonKernel_le_exponentialMajorant_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:19.316863+00:00
-- url     : https://prove2.me/submissions/39b3f26b-40ec-41cb-9e25-1ad21ef8bd3e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology


theorem solution
    {σ : ℝ} (hσ : 0 ≤ σ) (hσone : σ < 1)
    (T : ℝ) :
    stripPoissonKernel σ T ≤
      stripPoissonExponentialMajorant T := by
  unfold stripPoissonKernel stripPoissonExponentialMajorant
  have hp := Real.pi_pos
  have hθ1 : Real.pi / 2 ≤ stripAngle σ := by unfold stripAngle; nlinarith
  have hθ2 : stripAngle σ ≤ Real.pi := by unfold stripAngle; nlinarith
  have hcos : Real.cos (stripAngle σ) ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ1 (by linarith)
  have hsin1 := Real.sin_le_one (stripAngle σ)
  have hx : |Real.pi * T / 2| = Real.pi / 2 * |T| := by
    rw [show Real.pi * T / 2 = (Real.pi / 2) * T by ring, abs_mul, abs_of_pos (by positivity)]
  have hE := Real.exp_pos (Real.pi / 2 * |T|)
  have hE' := Real.exp_pos (-(Real.pi / 2 * |T|))
  have hch : Real.exp (Real.pi / 2 * |T|) / 2 ≤ Real.cosh (Real.pi * T / 2) := by
    rw [← Real.cosh_abs, hx, Real.cosh_eq]; linarith
  have hprod : Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  rw [div_le_iff₀ (by linarith)]
  have h1 : Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|) * (2 * Real.exp (Real.pi / 2 * |T|)) ≤
      Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|) *
        (4 * (Real.cosh (Real.pi * T / 2) - Real.cos (stripAngle σ))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|) * (2 * Real.exp (Real.pi / 2 * |T|)) = Real.pi := by
    rw [show Real.pi / 2 * Real.exp (-(Real.pi / 2) * |T|) * (2 * Real.exp (Real.pi / 2 * |T|)) =
      Real.pi * (Real.exp (-(Real.pi / 2) * |T|) * Real.exp (Real.pi / 2 * |T|)) by ring, hprod, mul_one]
  have := Real.pi_gt_three
  linarith


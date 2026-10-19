-- Prove2me | solution 2 for CohnElkies.saddleGaussianTailWeight_mul_gaussian_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:17:05.821296+00:00
-- url     : https://prove2.me/submissions/ac53da2e-d72b-40b9-8d3f-85e8eff9f1f4

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
    {k : ℝ} (hk : 0 < k) :
    Integrable
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2)) := by
  have h3 : Integrable (fun x : ℝ => x ^ (3:ℕ) * Real.exp (-k * x ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hk (s := ((3:ℕ):ℝ)) (by norm_num)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.rpow_natCast]
  have h0 := integrable_exp_neg_mul_sq hk
  refine (h0.add h3.norm).congr (Eventually.of_forall fun T => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _),
    saddleGaussianTailWeight]
  ring


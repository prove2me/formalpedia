-- Prove2me | solution 1 for CohnElkies.saddleGaussianTailWeight_mul_gaussian_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/b44a50ff-d11d-4dad-8fe1-a4af87e5f9f9

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
namespace CohnElkies
theorem _root_.solution
    {k : ℝ} (hk : 0 < k) :
    Integrable
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2)) := by
  have hzero := integrable_exp_neg_mul_sq hk
  have hthree := integrable_rpow_mul_exp_neg_mul_sq
    hk (s := (3 : ℝ)) (by norm_num)
  have hpolynomial : Integrable
      (fun T : ℝ => T ^ 3 * Real.exp (-k * T ^ 2)) := by
    simpa [Real.rpow_natCast] using! hthree
  have hsum := hzero.add hpolynomial.norm
  apply hsum.congr
  filter_upwards [] with T
  simp [saddleGaussianTailWeight, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), add_mul]
end CohnElkies

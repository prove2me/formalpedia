-- Prove2me | solution 1 for CohnElkies.saddleGaussianTailWeight_mul_exp_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/29c5503e-3ccd-450f-9b2e-a0d4672e0193

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_exp_neg_mul_abs
import Theorems.Thm_CohnElkies_integrable_abs_pow_mul_exp_neg_mul_abs

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
          Real.exp (-k * |T|)) := by
  have hzero := integrable_exp_neg_mul_abs hk
  have hthree := integrable_abs_pow_mul_exp_neg_mul_abs 3 hk
  have hsum := hzero.add hthree
  apply hsum.congr
  filter_upwards [] with T
  simp [saddleGaussianTailWeight, add_mul]
end CohnElkies

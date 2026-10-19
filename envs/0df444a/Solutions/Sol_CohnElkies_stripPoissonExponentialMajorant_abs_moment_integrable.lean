-- Prove2me | solution 1 for CohnElkies.stripPoissonExponentialMajorant_abs_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:33.627368+00:00
-- url     : https://prove2.me/submissions/8060edc4-c5d3-494d-a2e5-b769a000da22

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_abs_pow_mul_exp_neg_mul_abs

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable (fun T : ℝ =>
      stripPoissonExponentialMajorant T * |T|) := by
  have hmoment := integrable_abs_pow_mul_exp_neg_mul_abs
    1 (half_pos Real.pi_pos)
  have hscaled := hmoment.const_mul (Real.pi / 2)
  convert! hscaled using 1
  ext T
  simp [stripPoissonExponentialMajorant]
  ring
end CohnElkies

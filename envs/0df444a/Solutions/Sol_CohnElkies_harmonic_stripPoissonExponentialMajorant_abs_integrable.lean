-- Prove2me | solution 1 for CohnElkies.harmonic_stripPoissonExponentialMajorant_abs_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/be3ed49d-4724-414b-8ddf-b9e594fa1b23

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_abs_pow_mul_exp_neg_mul_abs

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable
      (fun T : ℝ =>
        stripPoissonExponentialMajorant T * |T|) := by
  have hbase :=
    integrable_abs_pow_mul_exp_neg_mul_abs 1
      (half_pos Real.pi_pos)
  have hconstant := hbase.const_mul (Real.pi / 2)
  convert! hconstant using 1
  ext T
  unfold stripPoissonExponentialMajorant
  norm_num
  ring
end CohnElkies

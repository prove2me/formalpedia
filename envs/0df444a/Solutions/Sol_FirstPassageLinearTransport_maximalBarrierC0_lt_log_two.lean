-- Prove2me | solution 1 for FirstPassageLinearTransport.maximalBarrierC0_lt_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:37.076462+00:00
-- url     : https://prove2.me/submissions/1d2a47cb-2f74-4850-bc1a-1cd3dbe845fe

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_logTwoThree_one_lt


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    maximalBarrierC0 < Real.log 2 := by
  have hlg : 1 < logTwoThree := logTwoThree_one_lt
  have hc : maximalBarrierC0 < 1 / 2 := by
    unfold maximalBarrierC0
    have hsq : 1 < logTwoThree ^ 2 := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hlogLower : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  exact hc.trans hlogLower
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.log_cosh_booleanOptimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:41:15.836852+00:00
-- url     : https://prove2.me/submissions/48af5616-4e8d-484e-b44b-f797dfde5da3

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_cosh_booleanOptimizer

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.log (Real.cosh (booleanOptimizer t)) =
      -Real.log 2 -
        (Real.log (1 / 2 + t) + Real.log (1 / 2 - t)) / 2 := by
  have hq : 0 < (1 / 2 : ℝ) - t := by linarith
  have hp : 0 < (1 / 2 : ℝ) + t := by linarith
  have hpq : 0 ≤ ((1 / 2 : ℝ) + t) * (1 / 2 - t) :=
    mul_nonneg hp.le hq.le
  have hsqrt : Real.sqrt (((1 / 2 : ℝ) + t) * (1 / 2 - t)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos hp hq))
  rw [cosh_booleanOptimizer ht0 ht1, one_div, Real.log_inv,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsqrt,
    Real.log_sqrt hpq, Real.log_mul (ne_of_gt hp) (ne_of_gt hq)]
  ring
end FirstPassageLinearTransport

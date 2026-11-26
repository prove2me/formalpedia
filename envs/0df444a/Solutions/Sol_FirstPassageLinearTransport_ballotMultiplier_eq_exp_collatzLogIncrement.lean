-- Prove2me | solution 1 for FirstPassageLinearTransport.ballotMultiplier_eq_exp_collatzLogIncrement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:55.38832+00:00
-- url     : https://prove2.me/submissions/2706f373-ba47-4860-8d05-3c816f2735c6

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (b : Bool) :
    ballotMultiplier b = Real.exp (collatzLogIncrement b) := by
  cases b with
  | false =>
      change (1 / 2 : ℝ) = Real.exp (-Real.log 2)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
  | true =>
      change (3 / 2 : ℝ) = Real.exp (Real.log 3 - Real.log 2)
      rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 3),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
end FirstPassageLinearTransport

-- Prove2me | solution 1 for FirstPassageLinearTransport.stirlingCore_eq_sqrt_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:58.401358+00:00
-- url     : https://prove2.me/submissions/56b386b9-bd49-4de7-9147-e4cd019fc7b7

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n : ℕ} (hn : 0 < n) :
    stirlingCore n =
      Real.sqrt (2 * n) *
        Real.exp ((n : ℝ) * (Real.log n - 1)) := by
  unfold stirlingCore
  congr 1
  have hnR : 0 < (n : ℝ) := by positivity
  calc
    ((n : ℝ) / Real.exp 1) ^ n =
        (Real.exp (Real.log n - 1)) ^ n := by
      congr 1
      rw [Real.exp_sub, Real.exp_log hnR]
    _ = Real.exp ((n : ℝ) * (Real.log n - 1)) := by
      rw [← Real.exp_nat_mul]
end FirstPassageLinearTransport

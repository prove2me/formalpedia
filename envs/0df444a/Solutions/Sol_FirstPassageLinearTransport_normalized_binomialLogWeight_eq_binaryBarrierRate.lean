-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_binomialLogWeight_eq_binaryBarrierRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:01.978319+00:00
-- url     : https://prove2.me/submissions/3a839a91-05fa-48eb-b1ed-e67119af6692

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_binomialLogWeight_eq_mul_binEntropy

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r k : ℕ} (hk : 0 < k) (hkr : k < r) :
    binomialLogWeight r k - (r : ℝ) * Real.log 2 =
      -((r : ℝ) *
        binaryBarrierRate ((k : ℝ) / (r : ℝ) - 1 / 2)) := by
  rw [binomialLogWeight_eq_mul_binEntropy hk hkr]
  unfold binaryBarrierRate
  congr 1
  congr 1
  ring
end FirstPassageLinearTransport

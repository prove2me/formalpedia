-- Prove2me | solution 1 for FirstPassageLinearTransport.binomialLogWeight_eq_mul_binEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:34.284198+00:00
-- url     : https://prove2.me/submissions/615a18d8-41c2-4200-a3af-d2cda85c4cfb

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
    {r k : ℕ} (hk : 0 < k) (hkr : k < r) :
    binomialLogWeight r k =
      (r : ℝ) * Real.binEntropy ((k : ℝ) / (r : ℝ)) := by
  have hr : 0 < r := hk.trans hkr
  have hrk : 0 < r - k := Nat.sub_pos_of_lt hkr
  have hrR : (r : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hrkR : ((r - k : ℕ) : ℝ) ≠ 0 := by positivity
  have hcomplement :
      1 - (k : ℝ) / (r : ℝ) =
        ((r - k : ℕ) : ℝ) / (r : ℝ) := by
    rw [Nat.cast_sub hkr.le]
    field_simp [hrR]
  unfold binomialLogWeight Real.binEntropy
  rw [hcomplement, Real.log_inv, Real.log_inv,
    Real.log_div hkR hrR, Real.log_div hrkR hrR,
    Nat.cast_sub hkr.le]
  field_simp [hrR]
  ring
end FirstPassageLinearTransport

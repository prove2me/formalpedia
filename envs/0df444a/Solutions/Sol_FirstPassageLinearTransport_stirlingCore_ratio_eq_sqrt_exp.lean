-- Prove2me | solution 1 for FirstPassageLinearTransport.stirlingCore_ratio_eq_sqrt_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:48.015598+00:00
-- url     : https://prove2.me/submissions/bdd2a7aa-cd10-4f17-97f4-39149929a3c0

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_stirlingCore_eq_sqrt_mul_exp

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r k : ℕ} (hk : 0 < k) (hkr : k < r) :
    stirlingCore r / (stirlingCore k * stirlingCore (r - k)) =
      Real.sqrt (2 * r) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * (r - k))) *
        Real.exp (binomialLogWeight r k) := by
  have hr : 0 < r := hk.trans hkr
  have hrk : 0 < r - k := Nat.sub_pos_of_lt hkr
  rw [stirlingCore_eq_sqrt_mul_exp hr,
    stirlingCore_eq_sqrt_mul_exp hk,
    stirlingCore_eq_sqrt_mul_exp hrk]
  have hexp :
      Real.exp ((r : ℝ) * (Real.log r - 1)) /
          (Real.exp ((k : ℝ) * (Real.log k - 1)) *
            Real.exp (((r - k : ℕ) : ℝ) * (Real.log (r - k) - 1))) =
        Real.exp (binomialLogWeight r k) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    unfold binomialLogWeight
    rw [Nat.cast_sub hkr.le]
    ring
  have factor_div (A B C E F G : ℝ) :
      A * E / ((B * F) * (C * G)) =
        A / (B * C) * (E / (F * G)) := by ring
  rw [Nat.cast_sub hkr.le] at hexp ⊢
  rw [factor_div, hexp]
end FirstPassageLinearTransport

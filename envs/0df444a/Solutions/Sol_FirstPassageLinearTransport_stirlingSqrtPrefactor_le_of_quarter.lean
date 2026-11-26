-- Prove2me | solution 1 for FirstPassageLinearTransport.stirlingSqrtPrefactor_le_of_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:22.511022+00:00
-- url     : https://prove2.me/submissions/38eaf716-46e0-4d82-bf84-c00068e1bed0

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
    {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (hkr : k < r)
    (hkLower : (r : ℝ) / 4 ≤ (k : ℝ))
    (hrkLower : (r : ℝ) / 4 ≤ ((r - k : ℕ) : ℝ)) :
    Real.sqrt (2 * r) /
        (Real.sqrt (2 * k) * Real.sqrt (2 * (r - k))) ≤
      4 / Real.sqrt r := by
  have hrR : 0 < (r : ℝ) := by positivity
  have hrk : 0 < r - k := Nat.sub_pos_of_lt hkr
  rw [Nat.cast_sub hkr.le] at hrkLower
  have hsqrtR : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrR
  have hkR : 0 < (k : ℝ) := by positivity
  have hrkR : 0 < (r : ℝ) - (k : ℝ) :=
    sub_pos.mpr (by exact_mod_cast hkr)
  have hden :
      0 < Real.sqrt (2 * k) * Real.sqrt (2 * ((r : ℝ) - k)) := by
    exact mul_pos (Real.sqrt_pos.2 (mul_pos (by norm_num) hkR))
      (Real.sqrt_pos.2 (mul_pos (by norm_num) hrkR))
  have hkSqrt :
      Real.sqrt ((r : ℝ) / 2) ≤ Real.sqrt (2 * k) := by
    apply Real.sqrt_le_sqrt
    calc
      (r : ℝ) / 2 = 2 * ((r : ℝ) / 4) := by ring
      _ ≤ 2 * (k : ℝ) := mul_le_mul_of_nonneg_left hkLower (by norm_num)
  have hrkSqrt :
      Real.sqrt ((r : ℝ) / 2) ≤
        Real.sqrt (2 * ((r : ℝ) - k)) := by
    apply Real.sqrt_le_sqrt
    calc
      (r : ℝ) / 2 = 2 * ((r : ℝ) / 4) := by ring
      _ ≤ 2 * ((r : ℝ) - k) :=
        mul_le_mul_of_nonneg_left hrkLower (by norm_num)
  have hdenLower :
      (r : ℝ) / 2 ≤
        Real.sqrt (2 * k) * Real.sqrt (2 * ((r : ℝ) - k)) := by
    calc
      (r : ℝ) / 2 =
          Real.sqrt ((r : ℝ) / 2) * Real.sqrt ((r : ℝ) / 2) := by
        rw [Real.mul_self_sqrt]
        positivity
      _ ≤ Real.sqrt (2 * k) * Real.sqrt (2 * ((r : ℝ) - k)) :=
        mul_le_mul hkSqrt hrkSqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hnumUpper :
      Real.sqrt (2 * r) ≤ 2 * Real.sqrt r := by
    calc
      Real.sqrt (2 * r) ≤ Real.sqrt (4 * r) := by
        apply Real.sqrt_le_sqrt
        push_cast
        linarith
      _ = Real.sqrt (4 : ℝ) * Real.sqrt r := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt r := by
        have hsqrtFour : Real.sqrt (4 : ℝ) = 2 := by
          have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num)
          have hnonneg := Real.sqrt_nonneg (4 : ℝ)
          nlinarith
        rw [hsqrtFour]
  apply (div_le_div_iff₀ hden hsqrtR).2
  have hleft :
      Real.sqrt (2 * r) * Real.sqrt r ≤ 2 * (r : ℝ) := by
    calc
      Real.sqrt (2 * r) * Real.sqrt r ≤
          (2 * Real.sqrt r) * Real.sqrt r :=
        mul_le_mul_of_nonneg_right hnumUpper (Real.sqrt_nonneg _)
      _ = 2 * (r : ℝ) := by
        rw [mul_assoc, Real.mul_self_sqrt hrR.le]
  have hright :
      2 * (r : ℝ) ≤
        4 * (Real.sqrt (2 * k) * Real.sqrt (2 * ((r : ℝ) - k))) := by
    linarith
  exact hleft.trans hright
end FirstPassageLinearTransport

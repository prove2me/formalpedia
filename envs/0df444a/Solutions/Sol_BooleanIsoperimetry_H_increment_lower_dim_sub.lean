-- Prove2me | solution 1 for BooleanIsoperimetry.H_increment_lower_dim_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:23.517487+00:00
-- url     : https://prove2.me/submissions/71c0ec16-30ea-4e84-9295-5d52d0d9f664

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_H_increment_lower
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    H n p + (n - p) ≤ H n (p + 1) := by
  have h := H_increment_lower n p hp
  have hmono : H n p ≤ H n (p + 1) := H_mono (by omega)
  by_cases hpn : p ≤ n
  · omega
  · have hzero : n - p = 0 := by omega
    rw [hzero]
    exact hmono
end BooleanIsoperimetry

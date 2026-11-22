-- Prove2me | solution 1 for BooleanIsoperimetry.H_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:07:18.850189+00:00
-- url     : https://prove2.me/submissions/8bc16c65-4fa6-48c8-b670-6892423edfcb

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_H_split_opt
public import Theorems.Thm_BooleanIsoperimetry_H_succ_slice


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n a b : ℕ) (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) :
    H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by
  rw [H_succ_slice]
  exact H_split_opt ha hb
end BooleanIsoperimetry

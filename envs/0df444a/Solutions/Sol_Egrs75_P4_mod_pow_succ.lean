-- Prove2me | solution 1 for Egrs75.P4.mod_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:26.24817+00:00
-- url     : https://prove2.me/submissions/f05e65d4-ff9e-435b-9138-47aaa4d9b589

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.P4
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
namespace Egrs75.P4
theorem _root_.solution (n q t : ℕ) :
    n % q ^ (t + 1) = n % q ^ t + q ^ t * (n / q ^ t % q) := by
  conv_lhs => rw [pow_succ]
  rw [Nat.mod_mul]
end Egrs75.P4

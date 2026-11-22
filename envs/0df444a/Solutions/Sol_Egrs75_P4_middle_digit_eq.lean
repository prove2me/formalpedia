-- Prove2me | solution 1 for Egrs75.P4.middle_digit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:40:20.998643+00:00
-- url     : https://prove2.me/submissions/0d1b4c84-5e65-4209-bf57-37848e7efd96

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Theorems.Thm_Egrs75_P4_not_strictGood_of_lt_leastGoodAbove
public import Theorems.Thm_Egrs75_RepairDV_digit_good_above_top


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
theorem _root_.solution {q n k : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n)
    (hjk : topBadIndex q n < k) (hk : k < leastGoodAbove hq hbad) :
    n / q ^ k % q = (q - 1) / 2 := by
  have hle : n / q ^ k % q ≤ (q - 1) / 2 := digit_good_above_top (by omega) hbad hjk
  have hge : ¬ (n / q ^ k % q < (q - 1) / 2) :=
    not_strictGood_of_lt_leastGoodAbove hq hbad hjk hk
  omega
end Egrs75.P4

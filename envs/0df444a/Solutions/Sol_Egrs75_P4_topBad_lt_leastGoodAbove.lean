-- Prove2me | solution 1 for Egrs75.P4.topBad_lt_leastGoodAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:22.984481+00:00
-- url     : https://prove2.me/submissions/b75e0ff2-7846-4d92-a15d-b1b24015da1b

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
theorem _root_.solution {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) :
    topBadIndex q n < leastGoodAbove hq hbad :=
  (Nat.find_spec (exists_strictGood_above hq hbad)).1
end Egrs75.P4

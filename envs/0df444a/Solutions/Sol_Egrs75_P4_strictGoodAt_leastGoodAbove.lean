-- Prove2me | solution 1 for Egrs75.P4.strictGoodAt_leastGoodAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:39.580911+00:00
-- url     : https://prove2.me/submissions/6e4e4822-28cc-46b9-840b-33a0e3f3e704

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
    StrictGoodAt q (leastGoodAbove hq hbad) n :=
  (Nat.find_spec (exists_strictGood_above hq hbad)).2
end Egrs75.P4

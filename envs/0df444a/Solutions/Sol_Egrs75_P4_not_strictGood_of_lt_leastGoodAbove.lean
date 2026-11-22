-- Prove2me | solution 1 for Egrs75.P4.not_strictGood_of_lt_leastGoodAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:25.784432+00:00
-- url     : https://prove2.me/submissions/5d951584-735d-49d9-9113-2a529656b3ab

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
theorem _root_.solution {q n k : ℕ} (hq : 3 ≤ q)
    (hbad : 0 < badCountQ q n) (hjk : topBadIndex q n < k)
    (hk : k < leastGoodAbove hq hbad) : ¬ StrictGoodAt q k n := by
  intro hcon
  -- `k` is strictly good and `> j`, so it is a witness for the `Nat.find` predicate,
  -- contradicting minimality of `leastGoodAbove`.
  exact Nat.find_min (exists_strictGood_above hq hbad) hk ⟨hjk, hcon⟩
end Egrs75.P4

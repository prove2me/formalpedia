-- Prove2me | solution 1 for Egrs75.P4.cond3_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:42:07.339236+00:00
-- url     : https://prove2.me/submissions/bea938a2-57a5-4cac-823a-92db41063615

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Theorems.Thm_Egrs75_P4_cond3_of_tail_small
public import Theorems.Thm_Egrs75_P4_topBad_lt_leastGoodAbove
public import Theorems.Thm_Egrs75_P4_strictGoodAt_leastGoodAbove
public import Theorems.Thm_Egrs75_P4_tail_ge

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
theorem _root_.solution {p q : ℕ} (_hp : 3 ≤ p) (hq : 3 ≤ q) (hpo : Odd p) (hqo : Odd q)
    (n m : ℕ) (hbad : 0 < badCountQ q n)
    (hTS : n % q ^ (leastGoodAbove hq hbad) < (p ^ m + 1) / 2) :
    ∃ i, topBadIndex q n < i ∧ n / q ^ i % q < (q - 1) / 2 ∧ q ^ i < p ^ m := by
  refine ⟨leastGoodAbove hq hbad, topBad_lt_leastGoodAbove hq hbad,
    strictGoodAt_leastGoodAbove hq hbad, ?_⟩
  -- condition (3): from the tail lower bound `B·G i + 1 ≤ T` and `T < S`.
  exact cond3_of_tail_small hq hpo hqo m _ _ (tail_ge hq hbad) hTS
end Egrs75.P4

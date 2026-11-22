-- Prove2me | solution 1 for Egrs75.P4.geomQ_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:51.857158+00:00
-- url     : https://prove2.me/submissions/0fbecf57-5dcf-4a5c-b5f3-cc5762cac5dd

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Theorems.Thm_Egrs75_P4_geomQ_golden

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
theorem _root_.solution {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    (q - 1) * geomQ q i = q ^ i - 1 := by
  have := geomQ_golden hq i; omega
end Egrs75.P4

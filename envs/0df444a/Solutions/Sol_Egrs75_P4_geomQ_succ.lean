-- Prove2me | solution 1 for Egrs75.P4.geomQ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:16.306871+00:00
-- url     : https://prove2.me/submissions/5bde86b0-977b-4dd6-9f0d-c05a4807b3c7

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
theorem _root_.solution (q i : ℕ) : geomQ q (i + 1) = geomQ q i + q ^ i := by
  unfold geomQ; rw [Finset.sum_range_succ]
end Egrs75.P4

-- Prove2me | solution 1 for Egrs75.P4.geomQ_golden
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:15.777518+00:00
-- url     : https://prove2.me/submissions/ae4508d5-ea9e-4d7e-88d0-da1f975f2d84

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
theorem _root_.solution {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    (q - 1) * geomQ q i + 1 = q ^ i := by
  unfold geomQ
  have hx : (q - 1) + 1 = q := by omega
  have h := geom_sum_mul_add (q - 1) i
  rw [hx] at h
  rw [mul_comm]; exact h
end Egrs75.P4

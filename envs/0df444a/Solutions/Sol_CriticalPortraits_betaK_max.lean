-- Prove2me | solution 1 for CriticalPortraits.betaK_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:44.2948+00:00
-- url     : https://prove2.me/submissions/650955a0-f35a-4745-acd3-4fa3bf47a10d

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m - 1) :
    Defc U (u.val % m) (u.val / m) u.val j ≠ 0 := by
  classical
  exact Nat.findGreatest_is_greatest (P := fun k => Defc U (u.val % m) (u.val / m) u.val k = 0)
    hj1 hj2
end CriticalPortraits

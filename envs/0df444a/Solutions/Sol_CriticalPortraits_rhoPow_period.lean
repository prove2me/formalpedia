-- Prove2me | solution 1 for CriticalPortraits.rhoPow_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:30.523766+00:00
-- url     : https://prove2.me/submissions/43677d64-1e87-4e69-9221-5806a4156cdb

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (S : Finset (ZMod (d * m))) : rhoPow d S = S := by
  unfold rhoPow
  have : ((d * m : ℕ) : ZMod (d * m)) = 0 := by rw [ZMod.natCast_self]
  rw [this]
  rw [show (Equiv.addRight (0 : ZMod (d * m))) = Equiv.refl _ from by ext x; simp]
  simp
end CriticalPortraits

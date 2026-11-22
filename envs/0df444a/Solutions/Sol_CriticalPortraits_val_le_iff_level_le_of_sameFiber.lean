-- Prove2me | solution 1 for CriticalPortraits.val_le_iff_level_le_of_sameFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:45.262792+00:00
-- url     : https://prove2.me/submissions/a383ca50-e0f5-45d4-a574-31b367c39829

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {N m : ℕ} {x y : ZMod N}
    (hxy : x.val % m = y.val % m) :
    x.val ≤ y.val ↔ x.val / m ≤ y.val / m := by
  constructor
  · intro h; exact Nat.div_le_div_right h
  · intro h
    have hx : x.val = (x.val / m) * m + x.val % m := (Nat.div_add_mod' x.val m).symm
    have hy : y.val = (y.val / m) * m + y.val % m := (Nat.div_add_mod' y.val m).symm
    rw [hxy] at hx
    have : (x.val / m) * m ≤ (y.val / m) * m := Nat.mul_le_mul_right m h
    omega
end CriticalPortraits

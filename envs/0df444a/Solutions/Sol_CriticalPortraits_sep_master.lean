-- Prove2me | solution 1 for CriticalPortraits.sep_master
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:44.811861+00:00
-- url     : https://prove2.me/submissions/c7250c0f-7650-4f4f-bd23-9f9fe326a34e

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
theorem _root_.solution {m : ℕ} {p q a c : ℕ} (hp : p < m) (_hq : q < m) (hac : a < c) :
    p + a * m < q + c * m := by
  have hstep : (a + 1) * m ≤ c * m := Nat.mul_le_mul_right m (by omega)
  have : a * m + m ≤ c * m := by rw [Nat.add_mul, Nat.one_mul] at hstep; omega
  omega
end CriticalPortraits

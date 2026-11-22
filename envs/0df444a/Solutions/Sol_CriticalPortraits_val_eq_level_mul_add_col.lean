-- Prove2me | solution 1 for CriticalPortraits.val_eq_level_mul_add_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:48.157481+00:00
-- url     : https://prove2.me/submissions/a3fb0e0d-6b72-4157-b149-4a250fb287a0

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
theorem _root_.solution {N : ℕ} (m : ℕ) (i : ZMod N) :
    i.val = (i.val / m) * m + i.val % m := (Nat.div_add_mod' i.val m).symm
end CriticalPortraits

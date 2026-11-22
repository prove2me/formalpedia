-- Prove2me | solution 1 for CriticalPortraits.level_injOn_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:45.851963+00:00
-- url     : https://prove2.me/submissions/af9c4105-ab49-4147-98db-508de4e6a3ff

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
theorem _root_.solution {N m : ℕ} [NeZero N] {x y : ZMod N}
    (hxy : x.val % m = y.val % m) (hlev : x.val / m = y.val / m) : x = y := by
  have hx : x.val = (x.val / m) * m + x.val % m := (Nat.div_add_mod' x.val m).symm
  have hy : y.val = (y.val / m) * m + y.val % m := (Nat.div_add_mod' y.val m).symm
  have : x.val = y.val := by rw [hx, hy, hxy, hlev]
  exact ZMod.val_injective _ this
end CriticalPortraits

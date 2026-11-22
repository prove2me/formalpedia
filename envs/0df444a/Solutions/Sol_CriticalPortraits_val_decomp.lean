-- Prove2me | solution 1 for CriticalPortraits.val_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:57.525667+00:00
-- url     : https://prove2.me/submissions/5707ab82-fe7a-447f-bbb3-2485ee569f77

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {N m : ℕ} (i : ZMod N) : i.val = (i.val % m) + (i.val / m) * m := by
  have := Nat.div_add_mod' i.val m; omega
end CriticalPortraits

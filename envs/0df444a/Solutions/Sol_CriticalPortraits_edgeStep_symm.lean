-- Prove2me | solution 1 for CriticalPortraits.edgeStep_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:07.306252+00:00
-- url     : https://prove2.me/submissions/8254a04d-8414-44a7-8efa-cdba5d68e3b0

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution [NeZero (d * m)] {P : Finset (Finset (ZMod (d * m)))}
    {u v : ZMod (d * m)} (h : edgeStep P u v) : edgeStep P v u := by
  obtain ⟨hu, hv, hcase⟩ := h; exact ⟨hv, hu, hcase.symm⟩
end CriticalPortraits

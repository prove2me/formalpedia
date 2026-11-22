-- Prove2me | solution 1 for CriticalPortraits.minVal_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:41.73409+00:00
-- url     : https://prove2.me/submissions/a4042dd9-1e5e-4ce8-ae17-9a25b2615dff

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
theorem _root_.solution {N : ℕ} {S S' : Finset (ZMod N)} (hS : S.Nonempty) (hS' : S'.Nonempty)
    (h : S = S') : minVal S hS = minVal S' hS' := by subst h; rfl
end CriticalPortraits

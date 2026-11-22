-- Prove2me | solution 1 for CriticalPortraits.reach_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:47.786186+00:00
-- url     : https://prove2.me/submissions/0f6bc3b5-0b38-45eb-9c90-b6d3712e2468

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
public import Theorems.Thm_CriticalPortraits_edgeStep_symm

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
    {u v : ZMod (d * m)} (h : Relation.ReflTransGen (edgeStep P) u v) :
    Relation.ReflTransGen (edgeStep P) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact Relation.ReflTransGen.head (edgeStep_symm hbc) ih
end CriticalPortraits

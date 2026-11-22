-- Prove2me | solution 1 for CriticalPortraits.bAdj_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:13.627745+00:00
-- url     : https://prove2.me/submissions/23803ba2-186b-4be0-a3d7-3cf855792448

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
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {U : Finset (ZMod (d * m))} {a b : ZMod (d * m)} (h : bAdj U a b) : bAdj U b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h
end CriticalPortraits

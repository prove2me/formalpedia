-- Prove2me | solution 1 for CriticalPortraits.bReach_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:50.278327+00:00
-- url     : https://prove2.me/submissions/394d60f9-e964-4a7a-9f45-7ef1d3b8da60

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
public import Theorems.Thm_CriticalPortraits_bAdj_symm

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {U : Finset (ZMod (d * m))} {a b : ZMod (d * m)} (h : bReach U a b) :
    bReach U b a := by
  unfold bReach at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hxy ih => exact Relation.ReflTransGen.head (bAdj_symm hxy) ih
end CriticalPortraits

-- Prove2me | solution 1 for CriticalPortraits.bReach_mem_bVerts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:15.670564+00:00
-- url     : https://prove2.me/submissions/2353d05e-f702-4163-93ec-12384e2e480c

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
public import Theorems.Thm_CriticalPortraits_bAdj_mem_bVerts

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {U : Finset (ZMod (d * m))} {x y : ZMod (d * m)}
    (hx : x ∈ bVerts U) (h : bReach U x y) : y ∈ bVerts U := by
  unfold bReach at h
  induction h with
  | refl => exact hx
  | @tail w z _ hwz _ => exact bAdj_mem_bVerts hwz
end CriticalPortraits

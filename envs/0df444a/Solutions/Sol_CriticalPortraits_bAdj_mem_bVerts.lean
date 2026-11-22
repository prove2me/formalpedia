-- Prove2me | solution 1 for CriticalPortraits.bAdj_mem_bVerts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:37.645298+00:00
-- url     : https://prove2.me/submissions/bacc43ad-13a2-446e-9feb-8176e37bad9d

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
public import Theorems.Thm_CriticalPortraits_mem_bVerts_of_mem
public import Theorems.Thm_CriticalPortraits_betaParent_mem_bVerts

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {U : Finset (ZMod (d * m))} {x y : ZMod (d * m)}
    (h : bAdj U x y) : y ∈ bVerts U := by
  rcases h with ⟨hyU, _, _⟩ | ⟨hxU, _, hyx⟩
  · exact mem_bVerts_of_mem hyU
  · rw [hyx]; exact betaParent_mem_bVerts hxU
end CriticalPortraits

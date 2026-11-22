-- Prove2me | solution 1 for CriticalPortraits.betaRoot_mem_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:28.592229+00:00
-- url     : https://prove2.me/submissions/24ea1609-d1b7-45c3-b0ea-8e6364f2d9b8

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
public import Theorems.Thm_CriticalPortraits_bReach_betaRoot
public import Theorems.Thm_CriticalPortraits_betaRoot_mem_bVerts

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) : betaRoot hd hm hcanon x ∈ betaBlock U x := by
  rw [mem_betaBlock]
  exact ⟨betaRoot_mem_bVerts hd hm hcanon hx, bReach_betaRoot hd hm hcanon x⟩
end CriticalPortraits

-- Prove2me | solution 1 for CriticalPortraits.betaRoot_bAdj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:34.906296+00:00
-- url     : https://prove2.me/submissions/b73d89fc-cb3c-425d-8796-dd6214e2f062

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
public import Theorems.Thm_CriticalPortraits_betaRoot_of_mem

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (h : bAdj U x y) : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y := by
  rcases h with ⟨hyU, _, hxy⟩ | ⟨hxU, _, hyx⟩
  · -- bEdge U x y: y ∈ U, x = betaParent y
    rw [hxy, ← betaRoot_of_mem hd hm hcanon hyU]
  · -- bEdge U y x: x ∈ U, y = betaParent x
    rw [hyx, ← betaRoot_of_mem hd hm hcanon hxU]
end CriticalPortraits

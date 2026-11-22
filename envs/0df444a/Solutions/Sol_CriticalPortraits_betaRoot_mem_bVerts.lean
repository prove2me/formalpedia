-- Prove2me | solution 1 for CriticalPortraits.betaRoot_mem_bVerts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:52.948224+00:00
-- url     : https://prove2.me/submissions/8e3f2e01-b8aa-4d49-900e-16ea3ca60d66

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
public import Theorems.Thm_CriticalPortraits_bReach_mem_bVerts

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
    (hx : x ∈ bVerts U) : betaRoot hd hm hcanon x ∈ bVerts U :=
  bReach_mem_bVerts hx (bReach_betaRoot hd hm hcanon x)
end CriticalPortraits

-- Prove2me | solution 1 for CriticalPortraits.betaBlock_sameFiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:44.261528+00:00
-- url     : https://prove2.me/submissions/bca479e6-9ba9-4a42-85cc-f4fc05fd123c

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
public import Theorems.Thm_CriticalPortraits_bReach_sameFiber

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
    (hy : y ∈ betaBlock U x) : y.val % m = x.val % m := by
  rw [mem_betaBlock] at hy
  obtain ⟨_, hreach⟩ := hy
  exact (bReach_sameFiber hd hm hcanon hreach).symm
end CriticalPortraits

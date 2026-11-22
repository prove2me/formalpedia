-- Prove2me | solution 1 for CriticalPortraits.betaRoot_min_in_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:45.912769+00:00
-- url     : https://prove2.me/submissions/2e5228f4-28b1-4b53-bd0f-22e0225c4aae

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
public import Theorems.Thm_CriticalPortraits_betaRoot_le
public import Theorems.Thm_CriticalPortraits_betaRoot_bReach

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
    (hy : y ∈ betaBlock U x) : (betaRoot hd hm hcanon x).val ≤ y.val := by
  rw [mem_betaBlock] at hy
  obtain ⟨_, hreach⟩ := hy
  have hroot_eq : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y :=
    betaRoot_bReach hd hm hcanon hreach
  rw [hroot_eq]
  exact betaRoot_le hd hm hcanon y
end CriticalPortraits

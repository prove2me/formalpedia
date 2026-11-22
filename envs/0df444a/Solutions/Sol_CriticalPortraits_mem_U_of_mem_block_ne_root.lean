-- Prove2me | solution 1 for CriticalPortraits.mem_U_of_mem_block_ne_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:46.413455+00:00
-- url     : https://prove2.me/submissions/b2b8eda1-1d8c-4fac-a7fc-c1c577ef537c

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
public import Theorems.Thm_CriticalPortraits_betaRoot_of_not_mem
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
    (hy : y ∈ betaBlock U x) (hne : y ≠ betaRoot hd hm hcanon x) : y ∈ U := by
  rw [mem_betaBlock] at hy
  obtain ⟨hyv, hreach⟩ := hy
  by_contra hyU
  -- y ∉ U ⇒ betaRoot y = y; but betaRoot y = betaRoot x
  have hself : betaRoot hd hm hcanon y = y := betaRoot_of_not_mem hd hm hcanon hyU
  have heq : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y :=
    betaRoot_bReach hd hm hcanon hreach
  simp_all
end CriticalPortraits

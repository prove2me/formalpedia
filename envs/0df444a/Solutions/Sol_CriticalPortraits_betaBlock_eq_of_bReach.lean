-- Prove2me | solution 1 for CriticalPortraits.betaBlock_eq_of_bReach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:33:25.826043+00:00
-- url     : https://prove2.me/submissions/f93e22c1-333a-4edf-9ab9-3b70f80d0a44

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
public import Theorems.Thm_CriticalPortraits_bReach_symm
public import Theorems.Thm_CriticalPortraits_bReach_trans

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {U : Finset (ZMod (d * m))} {v1 v2 : ZMod (d * m)}
    (h : bReach U v1 v2) : betaBlock U v1 = betaBlock U v2 := by
  ext z
  rw [mem_betaBlock, mem_betaBlock]
  constructor
  · rintro ⟨hzv, hreach⟩; exact ⟨hzv, bReach_trans (bReach_symm h) hreach⟩
  · rintro ⟨hzv, hreach⟩; exact ⟨hzv, bReach_trans h hreach⟩
end CriticalPortraits

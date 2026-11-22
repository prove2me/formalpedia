-- Prove2me | solution 1 for CriticalPortraits.betaRoot_bReach
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:10.014507+00:00
-- url     : https://prove2.me/submissions/dadc4d45-09e7-4b17-b00f-dcebbfb23388

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
public import Theorems.Thm_CriticalPortraits_betaRoot_bAdj

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
    (h : bReach U x y) : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y := by
  unfold bReach at h
  induction h with
  | refl => rfl
  | @tail w z _ hwz ih => rw [ih]; exact betaRoot_bAdj hd hm hcanon hwz
end CriticalPortraits

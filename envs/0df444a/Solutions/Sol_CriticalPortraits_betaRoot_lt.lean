-- Prove2me | solution 1 for CriticalPortraits.betaRoot_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:32:04.225191+00:00
-- url     : https://prove2.me/submissions/b16db0d5-79da-4b6e-8e1a-8b04e864db0a

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
public import Theorems.Thm_CriticalPortraits_betaRoot_le

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)} (hx : x ∈ U) :
    (betaRoot hd hm hcanon x).val < x.val := by
  rw [betaRoot_of_mem hd hm hcanon hx]
  have hlt : (betaParent U x).val < x.val :=
    betaParent_val_lt hd hm (survivor_level_pos hd hcanon hx)
  exact lt_of_le_of_lt (betaRoot_le hd hm hcanon (betaParent U x)) hlt
end CriticalPortraits

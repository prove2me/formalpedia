-- Prove2me | solution 1 for CriticalPortraits.bStep_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:31:55.948811+00:00
-- url     : https://prove2.me/submissions/587a9900-ef8a-4a7c-b90a-b67fd17dfb67

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
    (bStep U x).val < x.val := by
  unfold bStep; rw [dif_pos hx]
  exact betaParent_val_lt hd hm (survivor_level_pos hd hcanon hx)
end CriticalPortraits

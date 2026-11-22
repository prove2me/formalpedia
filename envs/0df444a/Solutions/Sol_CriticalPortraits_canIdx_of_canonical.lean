-- Prove2me | solution 1 for CriticalPortraits.canIdx_of_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:30.965419+00:00
-- url     : https://prove2.me/submissions/4079cfa4-f097-4f6a-a055-10ec12516f1b

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
open _root_.CriticalPortraits.Cycle
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (c : Finset (ZMod (d * m)))
    (hcard : c.card = d - 1) (hLC : LevelCanonical d m c) : canIdx hd hm c = 0 := by
  symm
  apply canIdx_eq hd hm c hcard hd
  rw [rhoPow_zero]; exact hLC
end CriticalPortraits

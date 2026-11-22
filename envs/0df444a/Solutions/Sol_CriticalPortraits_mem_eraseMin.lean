-- Prove2me | solution 1 for CriticalPortraits.mem_eraseMin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:44.38897+00:00
-- url     : https://prove2.me/submissions/492b1446-4df5-4411-af3d-d8c3d98b6a36

module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {N : ℕ} (S : Finset (ZMod N)) (h : S.Nonempty) (x : ZMod N) :
    x ∈ eraseMin S ↔ x ∈ S ∧ x ≠ minVal S h := by
  unfold eraseMin
  rw [dif_pos h, Finset.mem_erase]
  tauto
end CriticalPortraits

-- Prove2me | solution 1 for CriticalPortraits.minVal_level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:23.417619+00:00
-- url     : https://prove2.me/submissions/9fb5bc4a-45d2-4842-8ea2-cd913f3df72b

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
public import Theorems.Thm_CriticalPortraits_minVal_le
public import Theorems.Thm_CriticalPortraits_val_le_iff_level_le_of_sameFiber

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} {S : Finset (ZMod (d * m))}
    (hS : IsCriticalSet d m S) (h : S.Nonempty) :
    ∀ x ∈ S, (minVal S h).val / m ≤ x.val / m := by
  obtain ⟨⟨r, hr, hfib⟩, _⟩ := hS
  intro x hx
  have hsame : (minVal S h).val % m = x.val % m := by
    rw [hfib _ (minVal_mem S h), hfib _ hx]
  exact (val_le_iff_level_le_of_sameFiber hsame).mp (minVal_le S h x hx)
end CriticalPortraits

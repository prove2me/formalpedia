-- Prove2me | solution 1 for CriticalPortraits.minVal_lt_survivor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:28:43.627376+00:00
-- url     : https://prove2.me/submissions/016a2326-ee14-4b09-a9b8-b08adaa2f893

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
public import Theorems.Thm_CriticalPortraits_level_injOn_fiber
public import Theorems.Thm_CriticalPortraits_minVal_level_le

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {S : Finset (ZMod (d * m))} (hS : IsCriticalSet d m S) (h : S.Nonempty) :
    ∀ x ∈ eraseMin S, (minVal S h).val / m < x.val / m := by
  have : NeZero (d * m) := ⟨by positivity⟩
  obtain ⟨⟨r, hr, hfib⟩, hcard⟩ := hS
  intro x hx
  have hxS : x ∈ S := eraseMin_subset S hx
  have hxne : x ≠ minVal S h := by
    unfold eraseMin at hx
    simp_all
  have hsame : (minVal S h).val % m = x.val % m := by
    rw [hfib _ (minVal_mem S h), hfib _ hxS]
  have hle : (minVal S h).val / m ≤ x.val / m :=
    minVal_level_le ⟨⟨r, hr, hfib⟩, hcard⟩ h x hxS
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (level_injOn_fiber hsame heq).symm hxne
end CriticalPortraits

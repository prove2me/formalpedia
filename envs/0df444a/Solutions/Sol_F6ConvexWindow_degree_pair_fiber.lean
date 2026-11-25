-- Prove2me | solution 1 for F6ConvexWindow.degree_pair_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:45:24.212907+00:00
-- url     : https://prove2.me/submissions/80e7aa25-c1a9-441a-b889-1ce014e3edc3

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_antichain_inc
import Theorems.Thm_F6ConvexWindow_pair_antichain
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_ideal
attribute [local simp] F6ConvexWindow.mem_antichains

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (x : V) : (Inc x).card =
    (((antichains (V := V)).filter (fun T => T.card = 2)).filter (fun T => x ∈ T)).card := by
  classical
  apply card_bij (fun y _ => ({x, y} : Finset V))
  · intro y hy
    have hi := mem_Inc.mp hy
    have hne : x ≠ y := fun h => hi.1 (le_of_eq h)
    simp only [mem_filter, mem_antichains]
    exact ⟨⟨pair_antichain hi, by simp [hne]⟩, by simp⟩
  · intro a ha b hb he
    have hax : a ≠ x := fun h => (mem_Inc.mp ha).2 (le_of_eq h)
    have ham : a ∈ ({x, b} : Finset V) := he ▸ (by simp : a ∈ ({x, a} : Finset V))
    simpa [hax] using ham
  · intro T hT
    obtain ⟨⟨hTa, hTc⟩, hxT⟩ := mem_filter.mp hT |>.imp_left mem_filter.mp
    have hTa := mem_antichains.mp hTa
    obtain ⟨a, b, hab, hTab⟩ := card_eq_two.mp hTc
    subst T
    rcases (show x = a ∨ x = b by simpa using hxT) with rfl | rfl
    · have hi := antichain_inc hTa (by simp) (by simp) hab
      exact ⟨b, mem_Inc.mpr hi, rfl⟩
    · have hi := antichain_inc hTa (by simp) (by simp) hab.symm
      exact ⟨a, mem_Inc.mpr hi, by simp [pair_comm]⟩
end F6ConvexWindow

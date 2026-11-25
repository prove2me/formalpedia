-- Prove2me | solution 1 for F6ConvexWindow.triple_incomparables_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:36:15.183462+00:00
-- url     : https://prove2.me/submissions/f452a689-1d87-47d2-8ad3-31a45121749d

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_antichain_inc
import Theorems.Thm_F6ConvexWindow_triple_comparison
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
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {T : Finset V} (ht : Antichain T) (hc : T.card = 3) {x : V} (hx : x ∉ T) :
    (T.filter (IncRel x)).card ≤ 1 := by
  classical
  obtain ⟨y, hy, hxy⟩ := triple_comparison hw ht hc hx
  have hne : x ≠ y := fun h => hx (h.symm ▸ hy)
  have hchain : Chain (Inc x ∩ Inc y) := by
    rcases hxy with hxy | hyx
    · exact (hci x y (hxy.lt_of_ne hne)).1
    · simpa [inter_comm] using (hci y x (hyx.lt_of_ne hne.symm)).1
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨haT, hxa⟩ := mem_filter.mp ha
  obtain ⟨hbT, hxb⟩ := mem_filter.mp hb
  have hay : a ≠ y := by
    intro h
    subst a
    exact hxy.elim hxa.1 hxa.2
  have hby : b ≠ y := by
    intro h
    subst b
    exact hxy.elim hxb.1 hxb.2
  have ha' : a ∈ Inc x ∩ Inc y := by
    simp [hxa, antichain_inc ht hy haT hay.symm]
  have hb' : b ∈ Inc x ∩ Inc y := by
    simp [hxb, antichain_inc ht hy hbT hby.symm]
  exact (hchain a ha' b hb').elim (ht a haT b hbT) (fun h => (ht b hbT a haT h).symm)
end F6ConvexWindow

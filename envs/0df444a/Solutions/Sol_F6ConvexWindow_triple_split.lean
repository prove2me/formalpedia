-- Prove2me | solution 1 for F6ConvexWindow.triple_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:40:45.939494+00:00
-- url     : https://prove2.me/submissions/97a5e83e-4ce8-4ff3-a571-3cefd0fd7089

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_triple_comparison
import Theorems.Thm_F6ConvexWindow_triple_incomparables_le_one

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
    Below T x ∨ Above T x := by
  classical
  have hi := triple_incomparables_le_one hw hci ht hc hx
  have hsum := card_filter_add_card_filter_not (s := T) (p := IncRel x)
  have hcomp : 2 ≤ (T.filter (fun a => ¬ IncRel x a)).card := by omega
  obtain ⟨y, hy, hxy⟩ := triple_comparison hw ht hc hx
  have hne : ∀ a ∈ T, x ≠ a := fun a ha h => hx (h.symm ▸ ha)
  rcases hxy with hxy | hyx
  · left
    apply hcomp.trans
    apply card_le_card
    intro a ha
    obtain ⟨ha, hia⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨ha, ?_⟩
    have hax : ¬ a ≤ x := by
      intro h
      have hay := ht a ha y hy (h.trans hxy)
      have heq : x = a := le_antisymm (hay.symm ▸ hxy) h
      exact hne a ha heq
    have hxa : x ≤ a := by
      by_contra h
      exact hia ⟨h, hax⟩
    exact hxa.lt_of_ne (hne a ha)
  · right
    apply hcomp.trans
    apply card_le_card
    intro a ha
    obtain ⟨ha, hia⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨ha, ?_⟩
    have hxa : ¬ x ≤ a := by
      intro h
      have hya := ht y hy a ha (hyx.trans h)
      have heq : x = a := le_antisymm h (hya ▸ hyx)
      exact hne a ha heq
    have hax : a ≤ x := by
      by_contra h
      exact hia ⟨hxa, h⟩
    exact hax.lt_of_ne (hne a ha).symm
end F6ConvexWindow

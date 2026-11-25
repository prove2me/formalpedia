-- Prove2me | solution 1 for F6ConvexWindow.triple_intersection_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:01:24.36654+00:00
-- url     : https://prove2.me/submissions/b5de6ca4-88a4-4ac3-9feb-67178db9f16b

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_antichain_inc
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
    {S T : Finset V} (hs : Antichain S) (ht : Antichain T)
    (hsc : S.card = 3) (htc : T.card = 3) (hne : S ≠ T) : (S ∩ T).card ≤ 1 := by
  classical
  have hnsub : ¬ S ⊆ T := fun h => hne (eq_of_subset_of_card_le h (by omega))
  obtain ⟨x, hxS, hxT⟩ := not_subset.mp hnsub
  have hbound := triple_incomparables_le_one hw hci ht htc hxT
  apply (card_le_card (show S ∩ T ⊆ T.filter (IncRel x) from ?_)).trans hbound
  intro a ha
  obtain ⟨haS, haT⟩ := mem_inter.mp ha
  refine mem_filter.mpr ⟨haT, antichain_inc hs hxS haS ?_⟩
  intro h
  exact hxT (h.symm ▸ haT)
end F6ConvexWindow

-- Prove2me | solution 1 for F6ConvexWindow.overlapping_triples_comparable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:52:14.311301+00:00
-- url     : https://prove2.me/submissions/6877da95-7bdd-41ed-8536-d187979f14f7

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_earlier_exclusive_below
import Theorems.Thm_F6ConvexWindow_below_lt_other_of_inc
import Theorems.Thm_F6ConvexWindow_antichain_inc


set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (hs : IsTriple S) (ht : IsTriple T)
    (hST : ideal S ⊆ ideal T) (hover : (S ∩ T).Nonempty)
    {x y : V} (hxS : x ∈ S) (hxT : x ∉ T) (hyT : y ∈ T) (hyS : y ∉ S) : x < y := by
  obtain ⟨s, hsm⟩ := hover
  obtain ⟨hsS, hsT⟩ := mem_inter.mp hsm
  have hxs : x ≠ s := fun h => hxT (h.symm ▸ hsT)
  have hsy : s ≠ y := fun h => hyS (h ▸ hsS)
  exact below_lt_other_of_inc ht.2 (earlier_exclusive_below hw hci ht hST hxS hxT)
    hsT hyT hsy (antichain_inc hs.1 hxS hsS hxs)
end F6ConvexWindow

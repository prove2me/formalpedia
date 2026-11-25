-- Prove2me | solution 1 for F6ConvexWindow.earlier_prefix_lt_new
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:51:37.56831+00:00
-- url     : https://prove2.me/submissions/f3429017-c180-42b5-99a9-ab791e09e687

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_earlier_exclusive_below
import Theorems.Thm_F6ConvexWindow_later_exclusive_above
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_below_lt_above
import Theorems.Thm_F6ConvexWindow_ideal_subset_of_card_le
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6ConvexWindow.mem_tripleUnion

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) {x y : V}
    (hx : x ∈ tripleUnion G) (hxS : x ∉ S) (hyT : y ∈ T) (hyS : y ∉ S) : x < y := by
  obtain ⟨R, hRG, hxR⟩ := mem_tripleUnion.mp hx
  have hr := hg R hRG
  have hs := hg S hSG
  have hRS := ideal_subset_of_card_le hw hci hr.1 hs.1 hr.2 hs.2 (hSmax R hRG)
  exact below_lt_above hs.2 (earlier_exclusive_below hw hci hs hRS hxR hxS)
    (later_exclusive_above hw hci hs ht hST hyT hyS)
end F6ConvexWindow

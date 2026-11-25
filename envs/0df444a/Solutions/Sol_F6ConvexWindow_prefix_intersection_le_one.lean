-- Prove2me | solution 1 for F6ConvexWindow.prefix_intersection_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:56:58.885541+00:00
-- url     : https://prove2.me/submissions/e02d2bad-30b9-4f56-a9dd-12394493b952

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_prefix_overlap_eq_last
import Theorems.Thm_F6ConvexWindow_triple_intersection_le_one


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
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) (hTG : T ∉ G) :
    (tripleUnion G ∩ T).card ≤ 1 := by
  rw [inter_comm, prefix_overlap_eq_last hw hci hg hSG hSmax ht hST]
  exact triple_intersection_le_one hw hci ht.1 (hg S hSG).1 ht.2 (hg S hSG).2
    (fun h => hTG (h.symm ▸ hSG))
end F6ConvexWindow

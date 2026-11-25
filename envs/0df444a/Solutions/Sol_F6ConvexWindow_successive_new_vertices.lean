-- Prove2me | solution 1 for F6ConvexWindow.successive_new_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:35:53.740484+00:00
-- url     : https://prove2.me/submissions/f3145f9b-bc65-4fc7-ad85-83d9deeb91fa

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_prefix_intersection_le_one

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
    (T \ tripleUnion G).card = 2 ∨ (T \ tripleUnion G).card = 3 := by
  have hi := prefix_intersection_le_one hw hci hg hSG hSmax ht hST hTG
  have hc := card_sdiff_add_card_inter T (tripleUnion G)
  rw [inter_comm T, ht.2] at hc
  omega
end F6ConvexWindow

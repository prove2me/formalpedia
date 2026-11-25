-- Prove2me | solution 1 for F6ConvexWindow.ideal_subset_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:44:11.660373+00:00
-- url     : https://prove2.me/submissions/6fdcbfb0-a97d-4da0-b0d7-68edc317f7a5

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_triple_ideals_nested

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
    (hsc : S.card = 3) (htc : T.card = 3) (hc : (ideal S).card ≤ (ideal T).card) :
    ideal S ⊆ ideal T := by
  rcases triple_ideals_nested hw hci hs ht hsc htc with h | h
  · exact h
  · exact le_of_eq (eq_of_subset_of_card_le h hc).symm
end F6ConvexWindow

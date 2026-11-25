-- Prove2me | solution 1 for F6ConvexWindow.earlier_exclusive_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:45:25.430877+00:00
-- url     : https://prove2.me/submissions/4cd3d33f-3704-4b1f-a41b-00f2b73423c4

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_above_not_le
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_subset_ideal
import Theorems.Thm_F6ConvexWindow_triple_split
attribute [local simp] F6ConvexWindow.mem_ideal



set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {S T : Finset V} (ht : IsTriple T) (hST : ideal S ⊆ ideal T)
    {x : V} (hxS : x ∈ S) (hxT : x ∉ T) : Below T x := by
  rcases triple_split hw hci ht.1 ht.2 hxT with h | h
  · exact h
  · obtain ⟨t, htT, hxt⟩ := mem_ideal.mp (hST (subset_ideal S hxS))
    exact False.elim (above_not_le ht.1 h htT hxt)
end F6ConvexWindow

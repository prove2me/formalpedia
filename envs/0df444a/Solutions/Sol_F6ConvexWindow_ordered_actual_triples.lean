-- Prove2me | solution 1 for F6ConvexWindow.ordered_actual_triples
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:45:14.20902+00:00
-- url     : https://prove2.me/submissions/4d554f5a-0ac3-49e2-9a9b-108103d41caa

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_triplesDescending_toFinset
import Theorems.Thm_F6ConvexWindow_triplesDescending_strict
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6ConvexWindow.mem_tripleFamily

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V)) :
    ∃ L : List (Finset V), L.toFinset = tripleFamily ∧
      L.Pairwise (fun S T => ideal S ⊂ ideal T) := by
  refine ⟨(triplesDescending (tripleFamily (V := V))).reverse, ?_, ?_⟩
  · rw [List.toFinset_reverse, triplesDescending_toFinset]
  · exact (triplesDescending_strict hw hci tripleFamily
      (fun T hT => mem_tripleFamily.mp hT)).reverse
end F6ConvexWindow

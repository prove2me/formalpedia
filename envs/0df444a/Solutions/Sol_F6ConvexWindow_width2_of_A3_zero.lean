-- Prove2me | solution 1 for F6ConvexWindow.width2_of_A3_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:45:26.729878+00:00
-- url     : https://prove2.me/submissions/e5bddaac-e685-46b3-87c7-dee8e030b9cf

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6ConvexWindow.mem_tripleFamily
attribute [local simp] F6ConvexWindow.card_tripleFamily

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hzero : Ak (V := V) 3 = 0) :
    WidthLE (V := V) 2 := by
  intro T ht
  have hc := hw T ht
  by_contra h
  have h3 : T.card = 3 := by omega
  have hm : T ∈ tripleFamily := mem_tripleFamily.mpr ⟨ht, h3⟩
  have hp := card_pos.mpr ⟨T, hm⟩
  rw [card_tripleFamily, hzero] at hp
  omega
end F6ConvexWindow

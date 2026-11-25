-- Prove2me | solution 1 for F6ConvexWindow.chain_adjacent_overlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:37:58.838971+00:00
-- url     : https://prove2.me/submissions/f239dc6b-a318-4df0-8868-44f373f0b668

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_inc_symm
import Theorems.Thm_F6ConvexWindow_incomparability_interval
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_ideal
attribute [local simp] F6ConvexWindow.mem_antichains

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {C : Finset V} {x y : V}
    (hx : x ∈ C) (hmax : ∀ z ∈ C, z ≤ x) (hxy : x ≤ y) :
    (C.biUnion Inc) ∩ Inc y = Inc x ∩ Inc y := by
  classical
  apply Finset.ext
  intro z
  simp only [mem_inter, mem_biUnion, mem_Inc]
  constructor
  · rintro ⟨⟨a, ha, haz⟩, hyz⟩
    exact ⟨inc_symm (incomparability_interval (hmax a ha) hxy (inc_symm haz) (inc_symm hyz)), hyz⟩
  · rintro ⟨hxz, hyz⟩
    exact ⟨⟨x, hx, hxz⟩, hyz⟩
end F6ConvexWindow

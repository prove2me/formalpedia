-- Prove2me | solution 1 for F6ConvexWindow.pair_antichain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:39:54.224446+00:00
-- url     : https://prove2.me/submissions/e97acdaf-d5e9-4b30-a838-f964ef5c7f8a

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
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
theorem _root_.solution {x y : V} (hi : IncRel x y) : Antichain {x, y} := by
  classical
  intro a ha b hb hab
  simp only [mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact False.elim (hi.1 hab)
  · exact False.elim (hi.2 hab)
  · rfl
end F6ConvexWindow

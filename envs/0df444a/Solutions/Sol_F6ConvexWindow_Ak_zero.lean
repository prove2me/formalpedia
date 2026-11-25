-- Prove2me | solution 1 for F6ConvexWindow.Ak_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:03:08.901496+00:00
-- url     : https://prove2.me/submissions/ebd2e360-18a4-43f3-be82-dc9c761a99b5

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
theorem _root_.solution : Ak (V := V) 0 = 1 := by
  classical
  have he : (antichains (V := V)).filter (fun s => s.card = 0) = {∅} := by
    ext s
    simp only [mem_filter, mem_antichains, card_eq_zero, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨by intro x hx; simp at hx, rfl⟩
  unfold Ak
  rw [he]
  simp
end F6ConvexWindow

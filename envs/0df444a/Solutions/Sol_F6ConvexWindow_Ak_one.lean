-- Prove2me | solution 1 for F6ConvexWindow.Ak_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:03:16.852352+00:00
-- url     : https://prove2.me/submissions/0d9be650-3f84-4a66-8fe2-93ef8ec832f4

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
theorem _root_.solution : Ak (V := V) 1 = Fintype.card V := by
  classical
  have he : (antichains (V := V)).filter (fun s => s.card = 1) =
      (univ : Finset V).image (fun x => {x}) := by
    ext s
    simp only [mem_filter, mem_antichains, mem_image, mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := card_eq_one.mp h.2
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨?_, by simp⟩
      intro a ha b hb hab
      simpa only [mem_singleton] using (mem_singleton.mp ha).trans (mem_singleton.mp hb).symm
  unfold Ak
  rw [he, card_image_of_injective]
  · exact card_univ
  · intro a b hab
    simpa using hab
end F6ConvexWindow

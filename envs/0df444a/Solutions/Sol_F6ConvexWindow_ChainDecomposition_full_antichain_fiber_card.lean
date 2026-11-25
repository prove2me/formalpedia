-- Prove2me | solution 1 for F6ConvexWindow.ChainDecomposition.full_antichain_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:41:00.957191+00:00
-- url     : https://prove2.me/submissions/6e66ecfd-7a57-4aa8-98d2-b584b6cfe5a9

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_color_injective_on_antichain
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_ideal
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
namespace ChainDecomposition
theorem _root_.solution {k : ℕ}
    (d : ChainDecomposition (V := V) k) {T : Finset V}
    (ht : Antichain T) (hc : T.card = k) (i : Fin k) :
    (T.filter (fun x => d.color x = i)).card = 1 := by
  classical
  have hinj := d.color_injective_on_antichain ht
  have hcard : (T.image d.color).card = k := (card_image_of_injOn hinj).trans hc
  have hfull : T.image d.color = univ := eq_of_subset_of_card_le (subset_univ _) (by simp [hcard])
  have hi : i ∈ T.image d.color := hfull.symm ▸ mem_univ i
  obtain ⟨x, hx, hxi⟩ := mem_image.mp hi
  apply card_eq_one.mpr
  refine ⟨x, ?_⟩
  ext y
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hy, hyi⟩
    exact hinj hy hx (hyi.trans hxi.symm)
  · rintro rfl
    exact ⟨hx, hxi⟩
end ChainDecomposition
end F6ConvexWindow

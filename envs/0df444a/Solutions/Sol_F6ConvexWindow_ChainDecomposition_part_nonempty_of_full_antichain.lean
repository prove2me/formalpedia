-- Prove2me | solution 1 for F6ConvexWindow.ChainDecomposition.part_nonempty_of_full_antichain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:40:50.567224+00:00
-- url     : https://prove2.me/submissions/069b3226-ea0e-4e83-ac88-e34d35c6fbc7

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
open F6ConvexWindow.ChainDecomposition
variable {k : ℕ} (d : ChainDecomposition (V := V) k)
namespace F6ConvexWindow.ChainDecomposition
theorem _root_.solution {T : Finset V}
    (ht : Antichain T) (hc : T.card = k) (i : Fin k) : (d.part i).Nonempty := by
  classical
  have hcard : (T.image d.color).card = k := (card_image_of_injOn (d.color_injective_on_antichain ht)).trans hc
  have hfull : T.image d.color = univ := eq_of_subset_of_card_le (subset_univ _) (by simp [hcard])
  have hi : i ∈ T.image d.color := hfull.symm ▸ mem_univ i
  obtain ⟨x, hx, hxi⟩ := mem_image.mp hi
  exact ⟨x, (mem_part d).mpr hxi⟩
end F6ConvexWindow.ChainDecomposition

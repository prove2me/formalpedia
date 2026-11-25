-- Prove2me | solution 1 for F6ConvexWindow.ideal_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:36:43.780843+00:00
-- url     : https://prove2.me/submissions/9cf3a4c6-15ae-47b7-8fd7-76ea7cb7cd88

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_subset_ideal
attribute [local simp] F6ConvexWindow.mem_ideal

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {s t : Finset V} (hs : Antichain s) (ht : Antichain t)
    (h : ideal s = ideal t) : s = t := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_ideal.mp (h ▸ subset_ideal s hx)
    obtain ⟨z, hz, hyz⟩ := mem_ideal.mp (h.symm ▸ subset_ideal t hy)
    have hxz := hs x hx z hz (hxy.trans hyz)
    have hxy' : x = y := le_antisymm hxy (hxz ▸ hyz)
    exact hxy' ▸ hy
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_ideal.mp (h.symm ▸ subset_ideal t hx)
    obtain ⟨z, hz, hyz⟩ := mem_ideal.mp (h ▸ subset_ideal s hy)
    have hxz := ht x hx z hz (hxy.trans hyz)
    have hxy' : x = y := le_antisymm hxy (hxz ▸ hyz)
    exact hxy' ▸ hy
end F6ConvexWindow

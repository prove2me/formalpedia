-- Prove2me | solution 1 for F6ConvexWindow.no_reentry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:58:40.599229+00:00
-- url     : https://prove2.me/submissions/093813f0-e11a-477c-aac6-6fb29c47915a

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
theorem _root_.solution {s t u : Finset V} (hu : Antichain u)
    (hst : ideal s ⊆ ideal t) (htu : ideal t ⊆ ideal u)
    {x : V} (hxs : x ∈ s) (hxu : x ∈ u) : x ∈ t := by
  obtain ⟨y, hy, hxy⟩ := mem_ideal.mp (hst (subset_ideal s hxs))
  obtain ⟨z, hz, hyz⟩ := mem_ideal.mp (htu (subset_ideal t hy))
  have hxz := hu x hxu z hz (hxy.trans hyz)
  have hxy' : x = y := le_antisymm hxy (hxz ▸ hyz)
  exact hxy' ▸ hy
end F6ConvexWindow

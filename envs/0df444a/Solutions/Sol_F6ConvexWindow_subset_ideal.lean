-- Prove2me | solution 1 for F6ConvexWindow.subset_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:34:02.185829+00:00
-- url     : https://prove2.me/submissions/3f915926-2225-4dec-8752-f5782f72d935

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.mem_ideal

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (s : Finset V) : s ⊆ ideal s := by
  intro x hx
  exact mem_ideal.mpr ⟨x, hx, le_rfl⟩
end F6ConvexWindow

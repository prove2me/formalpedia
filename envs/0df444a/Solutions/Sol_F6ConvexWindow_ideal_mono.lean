-- Prove2me | solution 1 for F6ConvexWindow.ideal_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:36:36.799685+00:00
-- url     : https://prove2.me/submissions/80d224a9-7b44-4281-8246-9209837f2a76

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
theorem _root_.solution {s t : Finset V} (h : s ⊆ ideal t) : ideal s ⊆ ideal t := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_ideal.mp hx
  obtain ⟨z, hz, hyz⟩ := mem_ideal.mp (h hy)
  exact mem_ideal.mpr ⟨z, hz, hxy.trans hyz⟩
end F6ConvexWindow

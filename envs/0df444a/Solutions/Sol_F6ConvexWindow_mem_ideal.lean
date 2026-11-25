-- Prove2me | solution 1 for F6ConvexWindow.mem_ideal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:32:37.671988+00:00
-- url     : https://prove2.me/submissions/3c3af6d5-dcfc-48d3-bba0-d861d7645163

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
attribute [local simp] F6ConvexWindow.mem_Inc

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {s : Finset V} {x : V} :
    x ∈ ideal s ↔ ∃ y ∈ s, x ≤ y := by
  classical
  simp [ideal]
end F6ConvexWindow

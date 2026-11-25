-- Prove2me | solution 1 for F6ConvexWindow.mem_antichains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:33:59.736546+00:00
-- url     : https://prove2.me/submissions/9978c0e0-a4e2-496d-a9ca-b5a50003f720

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_ideal

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution {s : Finset V} :
    s ∈ antichains ↔ Antichain s := by
  classical
  simp [antichains]
end F6ConvexWindow

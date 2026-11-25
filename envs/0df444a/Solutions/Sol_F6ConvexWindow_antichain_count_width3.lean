-- Prove2me | solution 1 for F6ConvexWindow.antichain_count_width3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:16:01.742283+00:00
-- url     : https://prove2.me/submissions/9f66a93b-2a57-437c-89e7-5ab8d5c0692c

import Mathlib
import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_Ak_zero
import Theorems.Thm_F6ConvexWindow_Ak_one
import Theorems.Thm_F6ConvexWindow_antichain_count_decomposition
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
theorem _root_.solution (hw : WidthLE (V := V) 3) :
    totalAntichains (V := V) = 1 + Fintype.card V + Ak (V := V) 2 + Ak (V := V) 3 := by
  rw [antichain_count_decomposition 3 hw]
  simp [sum_range_succ, Ak_zero, Ak_one]
end F6ConvexWindow

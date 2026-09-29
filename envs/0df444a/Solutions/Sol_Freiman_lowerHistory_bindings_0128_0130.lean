-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0128_0130
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T16:13:45.193066+00:00
-- url     : https://prove2.me/submissions/4a3338d9-3d27-4db2-89d2-aff543fd45b3

import Theorems.Thm_Freiman_lowerHistory_bindings_0128_0129
import Theorems.Thm_Freiman_lowerHistory_bindings_0129_0130
import Mathlib.Tactic
open Freiman
theorem _root_.solution : lowerHistoryBindingBatch 128 130 := by
  intro i hlo hhi p hp
  by_cases h : i < 129
  · exact lowerHistory_bindings_0128_0129 i hlo h p hp
  · exact lowerHistory_bindings_0129_0130 i (by omega) hhi p hp
#print axioms solution

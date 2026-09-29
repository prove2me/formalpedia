-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1130_1140
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T08:22:42.827346+00:00
-- url     : https://prove2.me/submissions/6f16f06c-da09-4133-b8d8-10db9904c622

import Theorems.Thm_Freiman_lowerHistory_bindings_1130_1135
import Theorems.Thm_Freiman_lowerHistory_bindings_1135_1140
import Mathlib.Tactic
open Freiman
theorem solution : lowerHistoryBindingBatch 1130 1140 := by
  intro i hlo hhi p hp
  by_cases h : i < 1135
  · exact lowerHistory_bindings_1130_1135 i hlo h p hp
  exact lowerHistory_bindings_1135_1140 i (by omega) hhi p hp
#print axioms solution

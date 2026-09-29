-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1140_1150
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T08:24:36.787151+00:00
-- url     : https://prove2.me/submissions/ca70b644-80ff-448e-a3b4-5d086cdc0f6e

import Theorems.Thm_Freiman_lowerHistory_bindings_1140_1145
import Theorems.Thm_Freiman_lowerHistory_bindings_1145_1150
import Mathlib.Tactic
open Freiman
theorem solution : lowerHistoryBindingBatch 1140 1150 := by
  intro i hlo hhi p hp
  by_cases h : i < 1145
  · exact lowerHistory_bindings_1140_1145 i hlo h p hp
  exact lowerHistory_bindings_1145_1150 i (by omega) hhi p hp
#print axioms solution

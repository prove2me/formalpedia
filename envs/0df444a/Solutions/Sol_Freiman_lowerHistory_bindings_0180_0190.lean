-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0180_0190
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T19:35:46.166141+00:00
-- url     : https://prove2.me/submissions/2af3c4e9-61b3-4fb1-87dd-6328bbb535a4

import Theorems.Thm_Freiman_lowerHistory_bindings_0180_0185
import Theorems.Thm_Freiman_lowerHistory_bindings_0185_0190
import Mathlib.Tactic.IntervalCases
open Freiman

theorem solution : lowerHistoryBindingBatch 180 190 := by
  intro i hlo hhi p hp
  by_cases hm : i < 185
  · exact Freiman.lowerHistory_bindings_0180_0185 i hlo hm p hp
  · exact Freiman.lowerHistory_bindings_0185_0190 i (by omega) hhi p hp

#print axioms solution

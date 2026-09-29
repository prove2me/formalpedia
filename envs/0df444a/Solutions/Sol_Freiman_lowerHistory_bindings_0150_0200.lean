-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0150_0200
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T19:18:48.361193+00:00
-- url     : https://prove2.me/submissions/f6331d40-e26e-4da5-a18b-7492172836e2

import Theorems.Thm_Freiman_lowerHistory_bindings_0150_0160
import Theorems.Thm_Freiman_lowerHistory_bindings_0160_0170
import Theorems.Thm_Freiman_lowerHistory_bindings_0170_0180
import Theorems.Thm_Freiman_lowerHistory_bindings_0180_0190
import Theorems.Thm_Freiman_lowerHistory_bindings_0190_0200
import Mathlib.Tactic.IntervalCases
open Freiman
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

theorem solution : lowerHistoryBindingBatch 150 200 := by
  intro i hlo hhi p hp
  by_cases h160 : i < 160
  · exact Freiman.lowerHistory_bindings_0150_0160 i hlo h160 p hp
  by_cases h170 : i < 170
  · exact Freiman.lowerHistory_bindings_0160_0170 i (by omega) h170 p hp
  by_cases h180 : i < 180
  · exact Freiman.lowerHistory_bindings_0170_0180 i (by omega) h180 p hp
  by_cases h190 : i < 190
  · exact Freiman.lowerHistory_bindings_0180_0190 i (by omega) h190 p hp
  exact Freiman.lowerHistory_bindings_0190_0200 i (by omega) hhi p hp

#print axioms solution

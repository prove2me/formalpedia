-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0190_0200
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T19:37:12.044097+00:00
-- url     : https://prove2.me/submissions/4bc079f2-3eeb-4b88-b696-2124dd1b3a44

import Theorems.Thm_Freiman_lowerHistory_bindings_0190_0195
import Theorems.Thm_Freiman_lowerHistory_bindings_0195_0200
import Mathlib.Tactic.IntervalCases
open Freiman

theorem solution : lowerHistoryBindingBatch 190 200 := by
  intro i hlo hhi p hp
  by_cases hm : i < 195
  · exact Freiman.lowerHistory_bindings_0190_0195 i hlo hm p hp
  · exact Freiman.lowerHistory_bindings_0195_0200 i (by omega) hhi p hp

#print axioms solution

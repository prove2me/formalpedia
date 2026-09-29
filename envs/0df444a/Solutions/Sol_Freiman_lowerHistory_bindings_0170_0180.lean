-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0170_0180
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T19:35:46.413013+00:00
-- url     : https://prove2.me/submissions/67544c1b-ae17-4c68-ad48-6c0180f7d660

import Theorems.Thm_Freiman_lowerHistory_bindings_0170_0175
import Theorems.Thm_Freiman_lowerHistory_bindings_0175_0180
import Mathlib.Tactic.IntervalCases
open Freiman

theorem solution : lowerHistoryBindingBatch 170 180 := by
  intro i hlo hhi p hp
  by_cases hm : i < 175
  · exact Freiman.lowerHistory_bindings_0170_0175 i hlo hm p hp
  · exact Freiman.lowerHistory_bindings_0175_0180 i (by omega) hhi p hp

#print axioms solution

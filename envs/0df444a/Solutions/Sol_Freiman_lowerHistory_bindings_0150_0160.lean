-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0150_0160
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T19:34:58.378614+00:00
-- url     : https://prove2.me/submissions/a009c02f-fffc-4cbb-8be3-45fea2c2da22

import Theorems.Thm_Freiman_lowerHistory_bindings_0150_0155
import Theorems.Thm_Freiman_lowerHistory_bindings_0155_0160
import Mathlib.Tactic.IntervalCases
open Freiman

theorem solution : lowerHistoryBindingBatch 150 160 := by
  intro i hlo hhi p hp
  by_cases hm : i < 155
  · exact Freiman.lowerHistory_bindings_0150_0155 i hlo hm p hp
  · exact Freiman.lowerHistory_bindings_0155_0160 i (by omega) hhi p hp

#print axioms solution

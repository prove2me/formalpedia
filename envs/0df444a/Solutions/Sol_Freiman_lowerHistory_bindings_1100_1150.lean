-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1100_1150
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T08:14:54.526492+00:00
-- url     : https://prove2.me/submissions/ef8dcacd-4f53-481e-bb1d-5e9a6e183967

import Theorems.Thm_Freiman_lowerHistory_bindings_1100_1110
import Theorems.Thm_Freiman_lowerHistory_bindings_1110_1120
import Theorems.Thm_Freiman_lowerHistory_bindings_1120_1130
import Theorems.Thm_Freiman_lowerHistory_bindings_1130_1140
import Theorems.Thm_Freiman_lowerHistory_bindings_1140_1150
import Mathlib.Tactic
open Freiman
theorem solution : lowerHistoryBindingBatch 1100 1150 := by
  intro i hlo hhi p hp
  by_cases a : i < 1110
  · exact lowerHistory_bindings_1100_1110 i hlo a p hp
  by_cases b : i < 1120
  · exact lowerHistory_bindings_1110_1120 i (by omega) b p hp
  by_cases c : i < 1130
  · exact lowerHistory_bindings_1120_1130 i (by omega) c p hp
  by_cases d : i < 1140
  · exact lowerHistory_bindings_1130_1140 i (by omega) d p hp
  exact lowerHistory_bindings_1140_1150 i (by omega) hhi p hp
#print axioms solution

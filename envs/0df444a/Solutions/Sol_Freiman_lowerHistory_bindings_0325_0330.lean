-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0325_0330
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T22:19:49.299709+00:00
-- url     : https://prove2.me/submissions/1139be00-27ad-474e-9a72-bb4a9491417b

import Theorems.Thm_Freiman_lowerHistory_bindings_0325_0327
import Theorems.Thm_Freiman_lowerHistory_bindings_0327_0330
open Freiman
theorem solution : lowerHistoryBindingBatch 325 330 := by
  intro i hlo hhi p hp
  by_cases hc : i < 327
  · exact Freiman.lowerHistory_bindings_0325_0327 i hlo hc p hp
  · exact Freiman.lowerHistory_bindings_0327_0330 i (by omega) hhi p hp
#print axioms solution

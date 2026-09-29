-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1300_1350
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T06:51:25.831496+00:00
-- url     : https://prove2.me/submissions/2d294691-d561-4e6c-bfc7-2611a6129f46

import Theorems.Thm_Freiman_lowerHistory_bindings_1300_1305
import Theorems.Thm_Freiman_lowerHistory_bindings_1305_1310
import Theorems.Thm_Freiman_lowerHistory_bindings_1310_1315
import Theorems.Thm_Freiman_lowerHistory_bindings_1315_1320
import Theorems.Thm_Freiman_lowerHistory_bindings_1320_1325
import Theorems.Thm_Freiman_lowerHistory_bindings_1325_1330
import Theorems.Thm_Freiman_lowerHistory_bindings_1330_1335
import Theorems.Thm_Freiman_lowerHistory_bindings_1335_1340
import Theorems.Thm_Freiman_lowerHistory_bindings_1340_1345
import Theorems.Thm_Freiman_lowerHistory_bindings_1345_1350
open Freiman
theorem solution : lowerHistoryBindingBatch 1300 1350 := by
  intro i hlo hhi p hp
  by_cases h1300 : i < 1305
  · exact Freiman.lowerHistory_bindings_1300_1305 i (by omega) h1300 p hp
  by_cases h1305 : i < 1310
  · exact Freiman.lowerHistory_bindings_1305_1310 i (by omega) h1305 p hp
  by_cases h1310 : i < 1315
  · exact Freiman.lowerHistory_bindings_1310_1315 i (by omega) h1310 p hp
  by_cases h1315 : i < 1320
  · exact Freiman.lowerHistory_bindings_1315_1320 i (by omega) h1315 p hp
  by_cases h1320 : i < 1325
  · exact Freiman.lowerHistory_bindings_1320_1325 i (by omega) h1320 p hp
  by_cases h1325 : i < 1330
  · exact Freiman.lowerHistory_bindings_1325_1330 i (by omega) h1325 p hp
  by_cases h1330 : i < 1335
  · exact Freiman.lowerHistory_bindings_1330_1335 i (by omega) h1330 p hp
  by_cases h1335 : i < 1340
  · exact Freiman.lowerHistory_bindings_1335_1340 i (by omega) h1335 p hp
  by_cases h1340 : i < 1345
  · exact Freiman.lowerHistory_bindings_1340_1345 i (by omega) h1340 p hp
  exact Freiman.lowerHistory_bindings_1345_1350 i (by omega) hhi p hp
#print axioms solution

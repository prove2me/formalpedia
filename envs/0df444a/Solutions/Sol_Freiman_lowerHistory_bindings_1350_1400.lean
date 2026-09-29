-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1350_1400
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T07:17:01.916188+00:00
-- url     : https://prove2.me/submissions/45b27732-1ceb-40c7-81cc-2c1b3763d62b

import Theorems.Thm_Freiman_lowerHistory_bindings_1350_1355
import Theorems.Thm_Freiman_lowerHistory_bindings_1355_1360
import Theorems.Thm_Freiman_lowerHistory_bindings_1360_1365
import Theorems.Thm_Freiman_lowerHistory_bindings_1365_1370
import Theorems.Thm_Freiman_lowerHistory_bindings_1370_1375
import Theorems.Thm_Freiman_lowerHistory_bindings_1375_1380
import Theorems.Thm_Freiman_lowerHistory_bindings_1380_1385
import Theorems.Thm_Freiman_lowerHistory_bindings_1385_1390
import Theorems.Thm_Freiman_lowerHistory_bindings_1390_1395
import Theorems.Thm_Freiman_lowerHistory_bindings_1395_1400
open Freiman
theorem solution : lowerHistoryBindingBatch 1350 1400 := by
  intro i hlo hhi p hp
  by_cases h1350 : i < 1355
  · exact Freiman.lowerHistory_bindings_1350_1355 i (by omega) h1350 p hp
  by_cases h1355 : i < 1360
  · exact Freiman.lowerHistory_bindings_1355_1360 i (by omega) h1355 p hp
  by_cases h1360 : i < 1365
  · exact Freiman.lowerHistory_bindings_1360_1365 i (by omega) h1360 p hp
  by_cases h1365 : i < 1370
  · exact Freiman.lowerHistory_bindings_1365_1370 i (by omega) h1365 p hp
  by_cases h1370 : i < 1375
  · exact Freiman.lowerHistory_bindings_1370_1375 i (by omega) h1370 p hp
  by_cases h1375 : i < 1380
  · exact Freiman.lowerHistory_bindings_1375_1380 i (by omega) h1375 p hp
  by_cases h1380 : i < 1385
  · exact Freiman.lowerHistory_bindings_1380_1385 i (by omega) h1380 p hp
  by_cases h1385 : i < 1390
  · exact Freiman.lowerHistory_bindings_1385_1390 i (by omega) h1385 p hp
  by_cases h1390 : i < 1395
  · exact Freiman.lowerHistory_bindings_1390_1395 i (by omega) h1390 p hp
  exact Freiman.lowerHistory_bindings_1395_1400 i (by omega) hhi p hp
#print axioms solution

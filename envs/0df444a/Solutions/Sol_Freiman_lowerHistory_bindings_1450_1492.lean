-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1450_1492
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T07:53:33.604151+00:00
-- url     : https://prove2.me/submissions/6817731f-2626-4633-a33a-3e23fb95dea1

import Theorems.Thm_Freiman_lowerHistory_bindings_1450_1455
import Theorems.Thm_Freiman_lowerHistory_bindings_1455_1460
import Theorems.Thm_Freiman_lowerHistory_bindings_1460_1465
import Theorems.Thm_Freiman_lowerHistory_bindings_1465_1470
import Theorems.Thm_Freiman_lowerHistory_bindings_1470_1475
import Theorems.Thm_Freiman_lowerHistory_bindings_1475_1480
import Theorems.Thm_Freiman_lowerHistory_bindings_1480_1485
import Theorems.Thm_Freiman_lowerHistory_bindings_1485_1490
import Theorems.Thm_Freiman_lowerHistory_bindings_1490_1492
open Freiman
theorem solution : lowerHistoryBindingBatch 1450 1492 := by
  intro i hlo hhi p hp
  by_cases h1450 : i < 1455
  · exact Freiman.lowerHistory_bindings_1450_1455 i (by omega) h1450 p hp
  by_cases h1455 : i < 1460
  · exact Freiman.lowerHistory_bindings_1455_1460 i (by omega) h1455 p hp
  by_cases h1460 : i < 1465
  · exact Freiman.lowerHistory_bindings_1460_1465 i (by omega) h1460 p hp
  by_cases h1465 : i < 1470
  · exact Freiman.lowerHistory_bindings_1465_1470 i (by omega) h1465 p hp
  by_cases h1470 : i < 1475
  · exact Freiman.lowerHistory_bindings_1470_1475 i (by omega) h1470 p hp
  by_cases h1475 : i < 1480
  · exact Freiman.lowerHistory_bindings_1475_1480 i (by omega) h1475 p hp
  by_cases h1480 : i < 1485
  · exact Freiman.lowerHistory_bindings_1480_1485 i (by omega) h1480 p hp
  by_cases h1485 : i < 1490
  · exact Freiman.lowerHistory_bindings_1485_1490 i (by omega) h1485 p hp
  exact Freiman.lowerHistory_bindings_1490_1492 i (by omega) hhi p hp
#print axioms solution

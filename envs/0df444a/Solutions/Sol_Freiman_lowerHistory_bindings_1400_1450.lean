-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1400_1450
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T07:38:06.023864+00:00
-- url     : https://prove2.me/submissions/8cc5cb09-c410-4ef0-ab71-d160ad044c9b

import Theorems.Thm_Freiman_lowerHistory_bindings_1400_1405
import Theorems.Thm_Freiman_lowerHistory_bindings_1405_1410
import Theorems.Thm_Freiman_lowerHistory_bindings_1410_1415
import Theorems.Thm_Freiman_lowerHistory_bindings_1415_1420
import Theorems.Thm_Freiman_lowerHistory_bindings_1420_1425
import Theorems.Thm_Freiman_lowerHistory_bindings_1425_1430
import Theorems.Thm_Freiman_lowerHistory_bindings_1430_1435
import Theorems.Thm_Freiman_lowerHistory_bindings_1435_1440
import Theorems.Thm_Freiman_lowerHistory_bindings_1440_1445
import Theorems.Thm_Freiman_lowerHistory_bindings_1445_1450
open Freiman
theorem solution : lowerHistoryBindingBatch 1400 1450 := by
  intro i hlo hhi p hp
  by_cases h1400 : i < 1405
  · exact Freiman.lowerHistory_bindings_1400_1405 i (by omega) h1400 p hp
  by_cases h1405 : i < 1410
  · exact Freiman.lowerHistory_bindings_1405_1410 i (by omega) h1405 p hp
  by_cases h1410 : i < 1415
  · exact Freiman.lowerHistory_bindings_1410_1415 i (by omega) h1410 p hp
  by_cases h1415 : i < 1420
  · exact Freiman.lowerHistory_bindings_1415_1420 i (by omega) h1415 p hp
  by_cases h1420 : i < 1425
  · exact Freiman.lowerHistory_bindings_1420_1425 i (by omega) h1420 p hp
  by_cases h1425 : i < 1430
  · exact Freiman.lowerHistory_bindings_1425_1430 i (by omega) h1425 p hp
  by_cases h1430 : i < 1435
  · exact Freiman.lowerHistory_bindings_1430_1435 i (by omega) h1430 p hp
  by_cases h1435 : i < 1440
  · exact Freiman.lowerHistory_bindings_1435_1440 i (by omega) h1435 p hp
  by_cases h1440 : i < 1445
  · exact Freiman.lowerHistory_bindings_1440_1445 i (by omega) h1440 p hp
  exact Freiman.lowerHistory_bindings_1445_1450 i (by omega) hhi p hp
#print axioms solution

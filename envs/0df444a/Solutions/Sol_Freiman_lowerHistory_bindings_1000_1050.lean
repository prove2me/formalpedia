-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1000_1050
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T04:17:17.431798+00:00
-- url     : https://prove2.me/submissions/4b642e80-2060-4c62-bd4b-e4a1735da9a1

import Theorems.Thm_Freiman_lowerHistory_bindings_1000_1005
import Theorems.Thm_Freiman_lowerHistory_bindings_1005_1010
import Theorems.Thm_Freiman_lowerHistory_bindings_1010_1015
import Theorems.Thm_Freiman_lowerHistory_bindings_1015_1020
import Theorems.Thm_Freiman_lowerHistory_bindings_1020_1025
import Theorems.Thm_Freiman_lowerHistory_bindings_1025_1030
import Theorems.Thm_Freiman_lowerHistory_bindings_1030_1035
import Theorems.Thm_Freiman_lowerHistory_bindings_1035_1040
import Theorems.Thm_Freiman_lowerHistory_bindings_1040_1045
import Theorems.Thm_Freiman_lowerHistory_bindings_1045_1050
open Freiman
theorem solution : lowerHistoryBindingBatch 1000 1050 := by
  intro i hlo hhi p hp
  by_cases h1000 : i < 1005
  · exact Freiman.lowerHistory_bindings_1000_1005 i (by omega) h1000 p hp
  by_cases h1005 : i < 1010
  · exact Freiman.lowerHistory_bindings_1005_1010 i (by omega) h1005 p hp
  by_cases h1010 : i < 1015
  · exact Freiman.lowerHistory_bindings_1010_1015 i (by omega) h1010 p hp
  by_cases h1015 : i < 1020
  · exact Freiman.lowerHistory_bindings_1015_1020 i (by omega) h1015 p hp
  by_cases h1020 : i < 1025
  · exact Freiman.lowerHistory_bindings_1020_1025 i (by omega) h1020 p hp
  by_cases h1025 : i < 1030
  · exact Freiman.lowerHistory_bindings_1025_1030 i (by omega) h1025 p hp
  by_cases h1030 : i < 1035
  · exact Freiman.lowerHistory_bindings_1030_1035 i (by omega) h1030 p hp
  by_cases h1035 : i < 1040
  · exact Freiman.lowerHistory_bindings_1035_1040 i (by omega) h1035 p hp
  by_cases h1040 : i < 1045
  · exact Freiman.lowerHistory_bindings_1040_1045 i (by omega) h1040 p hp
  exact Freiman.lowerHistory_bindings_1045_1050 i (by omega) hhi p hp
#print axioms solution

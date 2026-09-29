-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1050_1100
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T05:28:14.596827+00:00
-- url     : https://prove2.me/submissions/51a7934c-da12-4359-9c61-d4958fba27e6

import Theorems.Thm_Freiman_lowerHistory_bindings_1050_1055
import Theorems.Thm_Freiman_lowerHistory_bindings_1055_1060
import Theorems.Thm_Freiman_lowerHistory_bindings_1060_1065
import Theorems.Thm_Freiman_lowerHistory_bindings_1065_1070
import Theorems.Thm_Freiman_lowerHistory_bindings_1070_1075
import Theorems.Thm_Freiman_lowerHistory_bindings_1075_1080
import Theorems.Thm_Freiman_lowerHistory_bindings_1080_1085
import Theorems.Thm_Freiman_lowerHistory_bindings_1085_1090
import Theorems.Thm_Freiman_lowerHistory_bindings_1090_1095
import Theorems.Thm_Freiman_lowerHistory_bindings_1095_1100
open Freiman
theorem solution : lowerHistoryBindingBatch 1050 1100 := by
  intro i hlo hhi p hp
  by_cases h1050 : i < 1055
  · exact Freiman.lowerHistory_bindings_1050_1055 i (by omega) h1050 p hp
  by_cases h1055 : i < 1060
  · exact Freiman.lowerHistory_bindings_1055_1060 i (by omega) h1055 p hp
  by_cases h1060 : i < 1065
  · exact Freiman.lowerHistory_bindings_1060_1065 i (by omega) h1060 p hp
  by_cases h1065 : i < 1070
  · exact Freiman.lowerHistory_bindings_1065_1070 i (by omega) h1065 p hp
  by_cases h1070 : i < 1075
  · exact Freiman.lowerHistory_bindings_1070_1075 i (by omega) h1070 p hp
  by_cases h1075 : i < 1080
  · exact Freiman.lowerHistory_bindings_1075_1080 i (by omega) h1075 p hp
  by_cases h1080 : i < 1085
  · exact Freiman.lowerHistory_bindings_1080_1085 i (by omega) h1080 p hp
  by_cases h1085 : i < 1090
  · exact Freiman.lowerHistory_bindings_1085_1090 i (by omega) h1085 p hp
  by_cases h1090 : i < 1095
  · exact Freiman.lowerHistory_bindings_1090_1095 i (by omega) h1090 p hp
  exact Freiman.lowerHistory_bindings_1095_1100 i (by omega) hhi p hp
#print axioms solution

-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1150_1200
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T05:49:56.631062+00:00
-- url     : https://prove2.me/submissions/d8bbcf97-5c60-491f-a620-d28726cc0d17

import Theorems.Thm_Freiman_lowerHistory_bindings_1150_1155
import Theorems.Thm_Freiman_lowerHistory_bindings_1155_1160
import Theorems.Thm_Freiman_lowerHistory_bindings_1160_1165
import Theorems.Thm_Freiman_lowerHistory_bindings_1165_1170
import Theorems.Thm_Freiman_lowerHistory_bindings_1170_1175
import Theorems.Thm_Freiman_lowerHistory_bindings_1175_1180
import Theorems.Thm_Freiman_lowerHistory_bindings_1180_1185
import Theorems.Thm_Freiman_lowerHistory_bindings_1185_1190
import Theorems.Thm_Freiman_lowerHistory_bindings_1190_1195
import Theorems.Thm_Freiman_lowerHistory_bindings_1195_1200
open Freiman
theorem solution : lowerHistoryBindingBatch 1150 1200 := by
  intro i hlo hhi p hp
  by_cases h1150 : i < 1155
  · exact Freiman.lowerHistory_bindings_1150_1155 i (by omega) h1150 p hp
  by_cases h1155 : i < 1160
  · exact Freiman.lowerHistory_bindings_1155_1160 i (by omega) h1155 p hp
  by_cases h1160 : i < 1165
  · exact Freiman.lowerHistory_bindings_1160_1165 i (by omega) h1160 p hp
  by_cases h1165 : i < 1170
  · exact Freiman.lowerHistory_bindings_1165_1170 i (by omega) h1165 p hp
  by_cases h1170 : i < 1175
  · exact Freiman.lowerHistory_bindings_1170_1175 i (by omega) h1170 p hp
  by_cases h1175 : i < 1180
  · exact Freiman.lowerHistory_bindings_1175_1180 i (by omega) h1175 p hp
  by_cases h1180 : i < 1185
  · exact Freiman.lowerHistory_bindings_1180_1185 i (by omega) h1180 p hp
  by_cases h1185 : i < 1190
  · exact Freiman.lowerHistory_bindings_1185_1190 i (by omega) h1185 p hp
  by_cases h1190 : i < 1195
  · exact Freiman.lowerHistory_bindings_1190_1195 i (by omega) h1190 p hp
  exact Freiman.lowerHistory_bindings_1195_1200 i (by omega) hhi p hp
#print axioms solution

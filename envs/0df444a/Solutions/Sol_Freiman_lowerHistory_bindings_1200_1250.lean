-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1200_1250
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T06:10:28.936504+00:00
-- url     : https://prove2.me/submissions/7b96d683-55d6-4295-afff-379f29c10911

import Theorems.Thm_Freiman_lowerHistory_bindings_1200_1205
import Theorems.Thm_Freiman_lowerHistory_bindings_1205_1210
import Theorems.Thm_Freiman_lowerHistory_bindings_1210_1215
import Theorems.Thm_Freiman_lowerHistory_bindings_1215_1220
import Theorems.Thm_Freiman_lowerHistory_bindings_1220_1225
import Theorems.Thm_Freiman_lowerHistory_bindings_1225_1230
import Theorems.Thm_Freiman_lowerHistory_bindings_1230_1235
import Theorems.Thm_Freiman_lowerHistory_bindings_1235_1240
import Theorems.Thm_Freiman_lowerHistory_bindings_1240_1245
import Theorems.Thm_Freiman_lowerHistory_bindings_1245_1250
open Freiman
theorem solution : lowerHistoryBindingBatch 1200 1250 := by
  intro i hlo hhi p hp
  by_cases h1200 : i < 1205
  · exact Freiman.lowerHistory_bindings_1200_1205 i (by omega) h1200 p hp
  by_cases h1205 : i < 1210
  · exact Freiman.lowerHistory_bindings_1205_1210 i (by omega) h1205 p hp
  by_cases h1210 : i < 1215
  · exact Freiman.lowerHistory_bindings_1210_1215 i (by omega) h1210 p hp
  by_cases h1215 : i < 1220
  · exact Freiman.lowerHistory_bindings_1215_1220 i (by omega) h1215 p hp
  by_cases h1220 : i < 1225
  · exact Freiman.lowerHistory_bindings_1220_1225 i (by omega) h1220 p hp
  by_cases h1225 : i < 1230
  · exact Freiman.lowerHistory_bindings_1225_1230 i (by omega) h1225 p hp
  by_cases h1230 : i < 1235
  · exact Freiman.lowerHistory_bindings_1230_1235 i (by omega) h1230 p hp
  by_cases h1235 : i < 1240
  · exact Freiman.lowerHistory_bindings_1235_1240 i (by omega) h1235 p hp
  by_cases h1240 : i < 1245
  · exact Freiman.lowerHistory_bindings_1240_1245 i (by omega) h1240 p hp
  exact Freiman.lowerHistory_bindings_1245_1250 i (by omega) hhi p hp
#print axioms solution

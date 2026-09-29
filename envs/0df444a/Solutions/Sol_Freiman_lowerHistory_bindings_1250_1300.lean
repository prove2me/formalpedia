-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1250_1300
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T06:31:46.727105+00:00
-- url     : https://prove2.me/submissions/ab02250f-9773-4726-849a-0d2d30002262

import Theorems.Thm_Freiman_lowerHistory_bindings_1250_1255
import Theorems.Thm_Freiman_lowerHistory_bindings_1255_1260
import Theorems.Thm_Freiman_lowerHistory_bindings_1260_1265
import Theorems.Thm_Freiman_lowerHistory_bindings_1265_1270
import Theorems.Thm_Freiman_lowerHistory_bindings_1270_1275
import Theorems.Thm_Freiman_lowerHistory_bindings_1275_1280
import Theorems.Thm_Freiman_lowerHistory_bindings_1280_1285
import Theorems.Thm_Freiman_lowerHistory_bindings_1285_1290
import Theorems.Thm_Freiman_lowerHistory_bindings_1290_1295
import Theorems.Thm_Freiman_lowerHistory_bindings_1295_1300
open Freiman
theorem solution : lowerHistoryBindingBatch 1250 1300 := by
  intro i hlo hhi p hp
  by_cases h1250 : i < 1255
  · exact Freiman.lowerHistory_bindings_1250_1255 i (by omega) h1250 p hp
  by_cases h1255 : i < 1260
  · exact Freiman.lowerHistory_bindings_1255_1260 i (by omega) h1255 p hp
  by_cases h1260 : i < 1265
  · exact Freiman.lowerHistory_bindings_1260_1265 i (by omega) h1260 p hp
  by_cases h1265 : i < 1270
  · exact Freiman.lowerHistory_bindings_1265_1270 i (by omega) h1265 p hp
  by_cases h1270 : i < 1275
  · exact Freiman.lowerHistory_bindings_1270_1275 i (by omega) h1270 p hp
  by_cases h1275 : i < 1280
  · exact Freiman.lowerHistory_bindings_1275_1280 i (by omega) h1275 p hp
  by_cases h1280 : i < 1285
  · exact Freiman.lowerHistory_bindings_1280_1285 i (by omega) h1280 p hp
  by_cases h1285 : i < 1290
  · exact Freiman.lowerHistory_bindings_1285_1290 i (by omega) h1285 p hp
  by_cases h1290 : i < 1295
  · exact Freiman.lowerHistory_bindings_1290_1295 i (by omega) h1290 p hp
  exact Freiman.lowerHistory_bindings_1295_1300 i (by omega) hhi p hp
#print axioms solution

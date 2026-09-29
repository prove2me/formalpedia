-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0250_0300
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T21:22:11.616984+00:00
-- url     : https://prove2.me/submissions/0888dd4c-dacb-48e9-a9f9-6d3b8aebc668

import Theorems.Thm_Freiman_lowerHistory_bindings_0250_0255
import Theorems.Thm_Freiman_lowerHistory_bindings_0255_0260
import Theorems.Thm_Freiman_lowerHistory_bindings_0260_0265
import Theorems.Thm_Freiman_lowerHistory_bindings_0265_0270
import Theorems.Thm_Freiman_lowerHistory_bindings_0270_0275
import Theorems.Thm_Freiman_lowerHistory_bindings_0275_0280
import Theorems.Thm_Freiman_lowerHistory_bindings_0280_0285
import Theorems.Thm_Freiman_lowerHistory_bindings_0285_0290
import Theorems.Thm_Freiman_lowerHistory_bindings_0290_0295
import Theorems.Thm_Freiman_lowerHistory_bindings_0295_0300
open Freiman

theorem solution : lowerHistoryBindingBatch 250 300 := by
  intro i hlo hhi p hp
  by_cases h255 : i < 255
  · exact Freiman.lowerHistory_bindings_0250_0255 i (by omega) h255 p hp
  by_cases h260 : i < 260
  · exact Freiman.lowerHistory_bindings_0255_0260 i (by omega) h260 p hp
  by_cases h265 : i < 265
  · exact Freiman.lowerHistory_bindings_0260_0265 i (by omega) h265 p hp
  by_cases h270 : i < 270
  · exact Freiman.lowerHistory_bindings_0265_0270 i (by omega) h270 p hp
  by_cases h275 : i < 275
  · exact Freiman.lowerHistory_bindings_0270_0275 i (by omega) h275 p hp
  by_cases h280 : i < 280
  · exact Freiman.lowerHistory_bindings_0275_0280 i (by omega) h280 p hp
  by_cases h285 : i < 285
  · exact Freiman.lowerHistory_bindings_0280_0285 i (by omega) h285 p hp
  by_cases h290 : i < 290
  · exact Freiman.lowerHistory_bindings_0285_0290 i (by omega) h290 p hp
  by_cases h295 : i < 295
  · exact Freiman.lowerHistory_bindings_0290_0295 i (by omega) h295 p hp
  exact Freiman.lowerHistory_bindings_0295_0300 i (by omega) hhi p hp
#print axioms solution

-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0350_0400
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T22:44:12.122831+00:00
-- url     : https://prove2.me/submissions/69f6e76f-d0c8-4b4b-aed1-e133ebfbf67f

import Theorems.Thm_Freiman_lowerHistory_bindings_0350_0355
import Theorems.Thm_Freiman_lowerHistory_bindings_0355_0360
import Theorems.Thm_Freiman_lowerHistory_bindings_0360_0365
import Theorems.Thm_Freiman_lowerHistory_bindings_0365_0370
import Theorems.Thm_Freiman_lowerHistory_bindings_0370_0375
import Theorems.Thm_Freiman_lowerHistory_bindings_0375_0380
import Theorems.Thm_Freiman_lowerHistory_bindings_0380_0385
import Theorems.Thm_Freiman_lowerHistory_bindings_0385_0390
import Theorems.Thm_Freiman_lowerHistory_bindings_0390_0395
import Theorems.Thm_Freiman_lowerHistory_bindings_0395_0400
open Freiman
theorem solution : lowerHistoryBindingBatch 350 400 := by
  intro i hlo hhi p hp
  by_cases h350 : i < 355
  · exact Freiman.lowerHistory_bindings_0350_0355 i (by omega) h350 p hp
  by_cases h355 : i < 360
  · exact Freiman.lowerHistory_bindings_0355_0360 i (by omega) h355 p hp
  by_cases h360 : i < 365
  · exact Freiman.lowerHistory_bindings_0360_0365 i (by omega) h360 p hp
  by_cases h365 : i < 370
  · exact Freiman.lowerHistory_bindings_0365_0370 i (by omega) h365 p hp
  by_cases h370 : i < 375
  · exact Freiman.lowerHistory_bindings_0370_0375 i (by omega) h370 p hp
  by_cases h375 : i < 380
  · exact Freiman.lowerHistory_bindings_0375_0380 i (by omega) h375 p hp
  by_cases h380 : i < 385
  · exact Freiman.lowerHistory_bindings_0380_0385 i (by omega) h380 p hp
  by_cases h385 : i < 390
  · exact Freiman.lowerHistory_bindings_0385_0390 i (by omega) h385 p hp
  by_cases h390 : i < 395
  · exact Freiman.lowerHistory_bindings_0390_0395 i (by omega) h390 p hp
  exact Freiman.lowerHistory_bindings_0395_0400 i (by omega) hhi p hp
#print axioms solution

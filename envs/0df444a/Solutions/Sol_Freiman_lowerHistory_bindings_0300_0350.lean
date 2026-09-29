-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0300_0350
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T22:22:02.618831+00:00
-- url     : https://prove2.me/submissions/9a0e3574-902d-4c1a-ad72-3e59f0774bd8

import Theorems.Thm_Freiman_lowerHistory_bindings_0300_0305
import Theorems.Thm_Freiman_lowerHistory_bindings_0305_0310
import Theorems.Thm_Freiman_lowerHistory_bindings_0310_0315
import Theorems.Thm_Freiman_lowerHistory_bindings_0315_0320
import Theorems.Thm_Freiman_lowerHistory_bindings_0320_0325
import Theorems.Thm_Freiman_lowerHistory_bindings_0325_0330
import Theorems.Thm_Freiman_lowerHistory_bindings_0330_0335
import Theorems.Thm_Freiman_lowerHistory_bindings_0335_0340
import Theorems.Thm_Freiman_lowerHistory_bindings_0340_0345
import Theorems.Thm_Freiman_lowerHistory_bindings_0345_0350
open Freiman
theorem solution : lowerHistoryBindingBatch 300 350 := by
  intro i hlo hhi p hp
  by_cases h300 : i < 305
  · exact Freiman.lowerHistory_bindings_0300_0305 i (by omega) h300 p hp
  by_cases h305 : i < 310
  · exact Freiman.lowerHistory_bindings_0305_0310 i (by omega) h305 p hp
  by_cases h310 : i < 315
  · exact Freiman.lowerHistory_bindings_0310_0315 i (by omega) h310 p hp
  by_cases h315 : i < 320
  · exact Freiman.lowerHistory_bindings_0315_0320 i (by omega) h315 p hp
  by_cases h320 : i < 325
  · exact Freiman.lowerHistory_bindings_0320_0325 i (by omega) h320 p hp
  by_cases h325 : i < 330
  · exact Freiman.lowerHistory_bindings_0325_0330 i (by omega) h325 p hp
  by_cases h330 : i < 335
  · exact Freiman.lowerHistory_bindings_0330_0335 i (by omega) h330 p hp
  by_cases h335 : i < 340
  · exact Freiman.lowerHistory_bindings_0335_0340 i (by omega) h335 p hp
  by_cases h340 : i < 345
  · exact Freiman.lowerHistory_bindings_0340_0345 i (by omega) h340 p hp
  exact Freiman.lowerHistory_bindings_0345_0350 i (by omega) hhi p hp
#print axioms solution

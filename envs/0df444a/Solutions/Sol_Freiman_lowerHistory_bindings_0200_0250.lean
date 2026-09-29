-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0200_0250
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T20:30:37.756915+00:00
-- url     : https://prove2.me/submissions/f772c446-7ffd-4655-8f43-6c7ac701bf5e

import Theorems.Thm_Freiman_lowerHistory_bindings_0200_0205
import Theorems.Thm_Freiman_lowerHistory_bindings_0205_0210
import Theorems.Thm_Freiman_lowerHistory_bindings_0210_0215
import Theorems.Thm_Freiman_lowerHistory_bindings_0215_0220
import Theorems.Thm_Freiman_lowerHistory_bindings_0220_0225
import Theorems.Thm_Freiman_lowerHistory_bindings_0225_0230
import Theorems.Thm_Freiman_lowerHistory_bindings_0230_0235
import Theorems.Thm_Freiman_lowerHistory_bindings_0235_0240
import Theorems.Thm_Freiman_lowerHistory_bindings_0240_0245
import Theorems.Thm_Freiman_lowerHistory_bindings_0245_0250
open Freiman
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
theorem solution : lowerHistoryBindingBatch 200 250 := by
  intro i hlo hhi p hp
  by_cases h205 : i < 205
  · exact Freiman.lowerHistory_bindings_0200_0205 i hlo h205 p hp
  by_cases h210 : i < 210
  · exact Freiman.lowerHistory_bindings_0205_0210 i (by omega) h210 p hp
  by_cases h215 : i < 215
  · exact Freiman.lowerHistory_bindings_0210_0215 i (by omega) h215 p hp
  by_cases h220 : i < 220
  · exact Freiman.lowerHistory_bindings_0215_0220 i (by omega) h220 p hp
  by_cases h225 : i < 225
  · exact Freiman.lowerHistory_bindings_0220_0225 i (by omega) h225 p hp
  by_cases h230 : i < 230
  · exact Freiman.lowerHistory_bindings_0225_0230 i (by omega) h230 p hp
  by_cases h235 : i < 235
  · exact Freiman.lowerHistory_bindings_0230_0235 i (by omega) h235 p hp
  by_cases h240 : i < 240
  · exact Freiman.lowerHistory_bindings_0235_0240 i (by omega) h240 p hp
  by_cases h245 : i < 245
  · exact Freiman.lowerHistory_bindings_0240_0245 i (by omega) h245 p hp
  exact Freiman.lowerHistory_bindings_0245_0250 i (by omega) hhi p hp
#print axioms solution

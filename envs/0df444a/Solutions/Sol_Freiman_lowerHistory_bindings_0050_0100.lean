-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0050_0100
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T10:42:32.561412+00:00
-- url     : https://prove2.me/submissions/9bb03daa-2987-4ea5-857d-af6aaa0cdaee

import Theorems.Thm_Freiman_lowerHistory_bindings_0050_0055
import Theorems.Thm_Freiman_lowerHistory_bindings_0055_0060
import Theorems.Thm_Freiman_lowerHistory_bindings_0060_0065
import Theorems.Thm_Freiman_lowerHistory_bindings_0065_0070
import Theorems.Thm_Freiman_lowerHistory_bindings_0070_0075
import Theorems.Thm_Freiman_lowerHistory_bindings_0075_0080
import Theorems.Thm_Freiman_lowerHistory_bindings_0080_0085
import Theorems.Thm_Freiman_lowerHistory_bindings_0085_0090
import Theorems.Thm_Freiman_lowerHistory_bindings_0090_0095
import Theorems.Thm_Freiman_lowerHistory_bindings_0095_0100
import Mathlib.Tactic
open Freiman
theorem solution : lowerHistoryBindingBatch 50 100 := by
  intro i hlo hhi p hp
  by_cases h55 : i < 55
  · exact lowerHistory_bindings_0050_0055 i hlo h55 p hp
  by_cases h60 : i < 60
  · exact lowerHistory_bindings_0055_0060 i (by omega) h60 p hp
  by_cases h65 : i < 65
  · exact lowerHistory_bindings_0060_0065 i (by omega) h65 p hp
  by_cases h70 : i < 70
  · exact lowerHistory_bindings_0065_0070 i (by omega) h70 p hp
  by_cases h75 : i < 75
  · exact lowerHistory_bindings_0070_0075 i (by omega) h75 p hp
  by_cases h80 : i < 80
  · exact lowerHistory_bindings_0075_0080 i (by omega) h80 p hp
  by_cases h85 : i < 85
  · exact lowerHistory_bindings_0080_0085 i (by omega) h85 p hp
  by_cases h90 : i < 90
  · exact lowerHistory_bindings_0085_0090 i (by omega) h90 p hp
  by_cases h95 : i < 95
  · exact lowerHistory_bindings_0090_0095 i (by omega) h95 p hp
  exact lowerHistory_bindings_0095_0100 i (by omega) hhi p hp
#print axioms solution

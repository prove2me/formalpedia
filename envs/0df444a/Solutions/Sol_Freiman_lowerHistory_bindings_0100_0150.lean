-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0100_0150
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T16:17:35.664982+00:00
-- url     : https://prove2.me/submissions/6c6c1ac5-b4f2-45da-b38f-4dca7e22b39e

import Theorems.Thm_Freiman_lowerHistory_bindings_0100_0105
import Theorems.Thm_Freiman_lowerHistory_bindings_0105_0110
import Theorems.Thm_Freiman_lowerHistory_bindings_0110_0115
import Theorems.Thm_Freiman_lowerHistory_bindings_0115_0120
import Theorems.Thm_Freiman_lowerHistory_bindings_0120_0125
import Theorems.Thm_Freiman_lowerHistory_bindings_0125_0130
import Theorems.Thm_Freiman_lowerHistory_bindings_0130_0135
import Theorems.Thm_Freiman_lowerHistory_bindings_0135_0140
import Theorems.Thm_Freiman_lowerHistory_bindings_0140_0145
import Theorems.Thm_Freiman_lowerHistory_bindings_0145_0150
import Mathlib.Tactic
open Freiman
theorem solution : lowerHistoryBindingBatch 100 150 := by
  intro i hlo hhi p hp
  by_cases h105 : i < 105
  · exact lowerHistory_bindings_0100_0105 i hlo h105 p hp
  by_cases h110 : i < 110
  · exact lowerHistory_bindings_0105_0110 i (by omega) h110 p hp
  by_cases h115 : i < 115
  · exact lowerHistory_bindings_0110_0115 i (by omega) h115 p hp
  by_cases h120 : i < 120
  · exact lowerHistory_bindings_0115_0120 i (by omega) h120 p hp
  by_cases h125 : i < 125
  · exact lowerHistory_bindings_0120_0125 i (by omega) h125 p hp
  by_cases h130 : i < 130
  · exact lowerHistory_bindings_0125_0130 i (by omega) h130 p hp
  by_cases h135 : i < 135
  · exact lowerHistory_bindings_0130_0135 i (by omega) h135 p hp
  by_cases h140 : i < 140
  · exact lowerHistory_bindings_0135_0140 i (by omega) h140 p hp
  by_cases h145 : i < 145
  · exact lowerHistory_bindings_0140_0145 i (by omega) h145 p hp
  exact lowerHistory_bindings_0145_0150 i (by omega) hhi p hp
#print axioms solution

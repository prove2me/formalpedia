-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0135_0140
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T16:05:00.136412+00:00
-- url     : https://prove2.me/submissions/bc8b8ef5-9fe4-49a0-9cd3-e93266426127

import Theorems.Thm_Freiman_lowerHistory_bindings_0135_0137
import Theorems.Thm_Freiman_lowerHistory_bindings_0137_0138
import Theorems.Thm_Freiman_lowerHistory_bindings_0138_0140
import Mathlib.Tactic
open Freiman
theorem _root_.solution : lowerHistoryBindingBatch 135 140 := by
  intro i hlo hhi p hp
  by_cases h : i < 137
  · exact lowerHistory_bindings_0135_0137 i hlo h p hp
  by_cases h' : i < 138
  · exact lowerHistory_bindings_0137_0138 i (by omega) h' p hp
  · exact lowerHistory_bindings_0138_0140 i (by omega) hhi p hp
#print axioms solution

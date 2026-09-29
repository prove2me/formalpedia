-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0125_0130
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T16:15:38.609506+00:00
-- url     : https://prove2.me/submissions/211694a5-95b3-495e-80fb-510fc9c538d7

import Theorems.Thm_Freiman_lowerHistory_bindings_0125_0128
import Theorems.Thm_Freiman_lowerHistory_bindings_0128_0130
import Mathlib.Tactic
open Freiman
theorem _root_.solution : lowerHistoryBindingBatch 125 130 := by
  intro i hlo hhi p hp
  by_cases h : i < 128
  · exact lowerHistory_bindings_0125_0128 i hlo h p hp
  · exact lowerHistory_bindings_0128_0130 i (by omega) hhi p hp
#print axioms solution

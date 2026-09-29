-- Prove2me | solution 1 for Freiman.lowerHistory_endpoint_semantics
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:35.432981+00:00
-- url     : https://prove2.me/submissions/e4cb4bb8-6691-4a70-8179-a1fc1dd6d8c7

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_equal_endpoint_cases
import Theorems.Thm_Freiman_lowerHistory_mixed_endpoint_cases
import Theorems.Thm_Freiman_lowerHistory_cf_value
import Theorems.Thm_Freiman_lowerHistory_width_threshold

open Freiman

theorem solution :
    LowerHistoryEndpointLaw := by
  intro base C hc words upper
  by_cases hp : lowerHistoryWordParity C words false = lowerHistoryWordParity C words true
  · exact lowerHistory_equal_endpoint_cases lowerHistory_width_threshold lowerHistory_cf_value base C hc words upper hp
  · exact lowerHistory_mixed_endpoint_cases lowerHistory_width_threshold lowerHistory_cf_value base C hc words upper hp

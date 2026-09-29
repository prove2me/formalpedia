-- Prove2me | solution 1 for Freiman.other22_all_bindings
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:41.210468+00:00
-- url     : https://prove2.me/submissions/cb1a30dc-bc23-4988-b22d-e40c6d24fe07

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_Freiman_other22_binding_context_1
import Theorems.Thm_Freiman_other22_binding_context_2
import Theorems.Thm_Freiman_other22_binding_context_3
import Theorems.Thm_Freiman_other22_binding_context_4
import Theorems.Thm_Freiman_other22_binding_context_5
import Theorems.Thm_Freiman_other22_binding_context_6

open Freiman

theorem solution :
    other22AllBindings := by
  intro k
  fin_cases k
  · exact other22_binding_context_1
  · exact other22_binding_context_2
  · exact other22_binding_context_3
  · exact other22_binding_context_4
  · exact other22_binding_context_5
  · exact other22_binding_context_6


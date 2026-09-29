-- Prove2me | solution 1 for Freiman.lower_guard_selected_extension
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:22.346401+00:00
-- url     : https://prove2.me/submissions/21ed658a-e856-4fb7-bccb-f47d4052f3d9

import Theorems.Thm_Freiman_lower_guard_offered
import Theorems.Thm_Freiman_lower_guard_case_extension
import Theorems.Thm_Freiman_lower_guard_boundary
import Theorems.Thm_Freiman_lower_guard_checks
import Theorems.Thm_Freiman_lower_guard_run_extension
import Definitions.Def_Freiman_lowerWordGuardData

open Freiman
theorem solution (p : LowerPair) (hp : lowerAdmissible p) (l : LowerLabel) (hl : lowerOffered p l) : lowerGuardExtensionData p l := by
  rcases lower_guard_offered p hp l hl with ⟨c,hc,hf,hm⟩ | ⟨hr,k,hk,rfl⟩
  · exact lower_guard_case_extension lower_guard_boundary p hp c (lower_guard_checks c hc) hf l hm
  · exact lower_guard_run_extension p hp hr k hk

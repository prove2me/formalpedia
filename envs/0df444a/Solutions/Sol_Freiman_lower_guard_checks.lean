-- Prove2me | solution 1 for Freiman.lower_guard_checks
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:41:22.597006+00:00
-- url     : https://prove2.me/submissions/11bb5752-617b-4941-b62a-2187c3894a8a

import Theorems.Thm_Freiman_lower_guard_catalog
import Theorems.Thm_Freiman_lower_guard_checks_equal
import Theorems.Thm_Freiman_lower_guard_checks_mixed
import Definitions.Def_Freiman_lowerWordGuardData

open Freiman
theorem solution : lowerGuardAllChecks := by
  intro c hc
  cases h : c.mixed
  · exact lower_guard_checks_equal lower_guard_catalog c hc h
  · exact lower_guard_checks_mixed lower_guard_catalog c hc h

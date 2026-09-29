-- Prove2me | solution 1 for Freiman.gap_maximum_forbidden
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:41:18.495259+00:00
-- url     : https://prove2.me/submissions/edd55b19-4efd-46c5-aa74-63b8e1c2e220

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_forbidden_application
import Theorems.Thm_Freiman_gap_maximum_forbidden_checks

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) : ∀ w ∈ gapMaximumForbidden, gapAvoids a w := by
  exact gap_forbidden_application gapMaximumForbidden gap_maximum_forbidden_checks a hc

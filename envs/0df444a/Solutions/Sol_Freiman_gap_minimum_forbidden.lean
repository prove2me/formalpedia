-- Prove2me | solution 1 for Freiman.gap_minimum_forbidden
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:41:18.469955+00:00
-- url     : https://prove2.me/submissions/fb752627-f92c-493b-a859-73ec332725e3

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_forbidden_application
import Theorems.Thm_Freiman_gap_minimum_forbidden_checks

open Freiman

theorem solution (a : ℤ → ℕ+) (hc : gapCapped a) : ∀ w ∈ gapMinimumForbidden, gapAvoids a w := by
  exact gap_forbidden_application gapMinimumForbidden gap_minimum_forbidden_checks a hc

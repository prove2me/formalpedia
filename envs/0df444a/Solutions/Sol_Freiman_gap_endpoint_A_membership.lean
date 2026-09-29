-- Prove2me | solution 1 for Freiman.gap_endpoint_A_membership
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:41:05.910877+00:00
-- url     : https://prove2.me/submissions/e84b12a8-8b48-41e5-bf3e-aafd30519495

import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_gap_centered_membership
import Theorems.Thm_Freiman_gap_extremizer_A_global

open Freiman

theorem solution : gapLeft ∈ symbolicMarkovSpectrum := by
  exact gap_centered_membership gapExtremizerA gapLeft gap_extremizer_A_global.1 gap_extremizer_A_global.2

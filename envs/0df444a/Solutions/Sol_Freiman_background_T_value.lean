-- Prove2me | solution 1 for Freiman.background_T_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:30.327909+00:00
-- url     : https://prove2.me/submissions/8c0f51c8-bdbe-4588-9bd0-b89033f02412

import Theorems.Thm_Freiman_gap_periodic_evaluation
import Theorems.Thm_Freiman_background_T_fixedpoint

open Freiman

theorem solution :
    cfValue backgroundT = -1 + Real.sqrt 462 / 12 := by
  have h := background_T_fixedpoint
  simpa only [backgroundT] using gap_periodic_evaluation [1,3,1,3,1,2] (by decide)
    (-1 + Real.sqrt 462 / 12) ⟨h.1, h.2.1⟩ h.2.2


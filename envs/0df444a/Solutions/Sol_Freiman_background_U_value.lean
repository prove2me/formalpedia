-- Prove2me | solution 1 for Freiman.background_U_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:29:41.826985+00:00
-- url     : https://prove2.me/submissions/0b8eb6dd-247c-4cd6-8b30-8087843179c7

import Theorems.Thm_Freiman_gap_periodic_evaluation
import Theorems.Thm_Freiman_background_U_fixedpoint

open Freiman

theorem solution :
    cfValue backgroundU = (2 * Real.sqrt 462 - 28) / 19 := by
  have h := background_U_fixedpoint
  simpa only [backgroundU] using gap_periodic_evaluation [1,3,1,2,1,3] (by decide)
    ((2 * Real.sqrt 462 - 28) / 19) ⟨h.1, h.2.1⟩ h.2.2


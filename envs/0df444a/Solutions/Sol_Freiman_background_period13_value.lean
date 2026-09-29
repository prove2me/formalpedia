-- Prove2me | solution 1 for Freiman.background_period13_value
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:29:42.201661+00:00
-- url     : https://prove2.me/submissions/9eb31ad4-875c-496a-b43b-90c26916fe44

import Theorems.Thm_Freiman_gap_periodic_evaluation
import Theorems.Thm_Freiman_background_period13_fixedpoint

open Freiman

theorem solution :
    cfValue backgroundPeriod13 = (Real.sqrt 21 - 3) / 2 := by
  have h := background_period13_fixedpoint
  simpa only [backgroundPeriod13] using gap_periodic_evaluation [1,3] (by decide)
    ((Real.sqrt 21 - 3) / 2) ⟨h.1, h.2.1⟩ h.2.2


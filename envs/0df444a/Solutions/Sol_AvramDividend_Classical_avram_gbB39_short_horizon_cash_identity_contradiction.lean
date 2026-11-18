-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB39_short_horizon_cash_identity_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T15:40:52.16395+00:00
-- url     : https://prove2.me/submissions/b926c3b4-81fd-4ec9-9652-94999e104551

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB36_short_horizon_sigma1_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- The short-horizon original cash identity contradicts the fixed-j cash cap. -/
theorem solution (y F wC N : ℝ)
  (hylo : (5 / 44 : ℝ) ≤ y) (hyhi : y ≤ (1 / 8 : ℝ))
  (hCash : F - wC - N =
    (193419 / 968 : ℝ) * (1 - Real.exp (-(1 / 100000 : ℝ))) +
      Real.exp (-(1 / 100000 : ℝ)) *
        (y - 4 * y ^ 2 - 15 / 242) - (1 / 1936 : ℝ)) :
  ¬ F - wC ≤ N + (1 / 1936 : ℝ) := by
  have hGap := avram_gbB36_short_horizon_sigma1_gap y hylo hyhi
  intro hBound
  linarith

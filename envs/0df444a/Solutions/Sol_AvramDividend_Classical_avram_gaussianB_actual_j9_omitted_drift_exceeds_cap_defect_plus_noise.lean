-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_actual_j9_omitted_drift_exceeds_cap_defect_plus_noise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:16:53.392113+00:00
-- url     : https://prove2.me/submissions/85b4d984-ecbe-4607-992d-7789959fd4ec

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
/-- Exact strict rational drift margin after fixed-band cap defect and noise. -/
theorem solution :
    0 < (2 : ℝ) * (1 / 1000 : ℝ) -
      (((((2 * (1 / 8 : ℝ) - 4 * (1 / 8 : ℝ) ^ 2) -
         (2 * (5 / 44 : ℝ) - 4 * (5 / 44 : ℝ) ^ 2)) -
         ((1 / 8 : ℝ) - (5 / 44 : ℝ))) +
        (1 / 4000 : ℝ)) ) := by norm_num

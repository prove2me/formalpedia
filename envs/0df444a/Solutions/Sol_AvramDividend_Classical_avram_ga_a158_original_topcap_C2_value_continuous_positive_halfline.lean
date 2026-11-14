-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:39:05.395429+00:00
-- url     : https://prove2.me/submissions/e899cd60-0556-4c01-819f-f1fe78076afb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ContinuousOn w (Ioi (0 : ℝ)) := by
  have hSet : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} = Ioi (0 : ℝ) := by
    ext y
    simp [hTopCap]
  rw [hSet] at hw_smooth
  exact hw_smooth.continuousOn

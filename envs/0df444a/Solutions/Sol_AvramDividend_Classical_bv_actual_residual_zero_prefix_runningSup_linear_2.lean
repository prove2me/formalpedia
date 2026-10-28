-- Prove2me | solution 2 for AvramDividend.Classical.bv_actual_residual_zero_prefix_runningSup_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:05:31.331608+00:00
-- url     : https://prove2.me/submissions/51f3f3c2-8cc8-4aab-9f56-88676f3c03a4

import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Zero drift deficit throughout a time interval gives a linear record path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (ω : Ω) (t : ℝ≥0)
    (hHistory : ∀ s : ℝ≥0, s ≤ t →
      (s : ℝ) * X.drift - X.X s ω = 0) :
    ∀ u : ℝ≥0, u ≤ t →
      runningSup X u ω = X.drift * (u : ℝ) := by
  have hDrift : 0 ≤ X.drift :=
    le_of_lt (bv_standing_drift_pos X hStanding hBV).1
  intro u hu
  apply runningSup_linear_of_linear_capital_prefix X ω u hDrift
  intro s hs
  have hZero := hHistory s (le_trans hs hu)
  rw [mul_comm (s : ℝ) X.drift] at hZero
  linarith

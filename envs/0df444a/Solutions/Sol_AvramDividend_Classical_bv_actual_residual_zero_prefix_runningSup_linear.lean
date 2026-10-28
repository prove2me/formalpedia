-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_residual_zero_prefix_runningSup_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:04:49.256728+00:00
-- url     : https://prove2.me/submissions/16f3dce0-9d29-471e-86cc-ec007f587c2f

import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A zero residual prefix forces the actual running record to equal the drift prefix. -/
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
  intro u hu
  have hLinear : ∀ s : ℝ≥0, s ≤ u →
      X.X s ω = X.drift * (s : ℝ) := by
    intro s hs
    have h := hHistory s (hs.trans hu)
    rw [mul_comm] at h
    linarith
  exact runningSup_linear_of_linear_capital_prefix X ω u
    (bv_standing_drift_pos X hStanding hBV).1.le hLinear

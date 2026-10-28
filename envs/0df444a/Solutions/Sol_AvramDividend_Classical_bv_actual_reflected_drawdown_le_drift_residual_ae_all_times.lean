-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_reflected_drawdown_le_drift_residual_ae_all_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:31:01.418794+00:00
-- url     : https://prove2.me/submissions/af2a858a-ef61-4712-a1e0-919d415b02a2

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_all_times
import Theorems.Thm_AvramDividend_Classical_runningSup_le_drift_of_upper_bv_path
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Under BV Standing, actual drawdown is bounded pathwise by the drift deficit at every time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      drawdown X t ω ≤ (t : ℝ) * X.drift - X.X t ω := by
  filter_upwards [bv_actual_levy_drift_upper_ae_all_times X hBV] with ω hw
  intro t
  have hPath : ∀ u : ℝ≥0, u ≤ t →
      X.X u ω ≤ X.drift * (u : ℝ) := by
    intro u _
    simpa only [mul_comm] using hw u
  have hS := runningSup_le_drift_of_upper_bv_path X ω t
    (bv_standing_drift_pos X hStanding hBV).1.le hPath
  dsimp [drawdown, reflectedSup]
  linarith

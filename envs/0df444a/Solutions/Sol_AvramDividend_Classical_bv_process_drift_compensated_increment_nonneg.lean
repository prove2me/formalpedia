-- Prove2me | solution 1 for AvramDividend.Classical.bv_process_drift_compensated_increment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:16:54.639981+00:00
-- url     : https://prove2.me/submissions/e4da50f6-5164-480f-a723-6f7a29d69052

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_fixed_times
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Drift compensation has nonnegative increments for a bounded-variation Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂P,
      0 ≤ X.drift * ((t : ℝ) - (s : ℝ)) - (X.X t ω - X.X s ω) := by
  filter_upwards [bv_actual_levy_drift_increment_ae_fixed_times
      X hBV s t hst] with ω hω
  rw [NNReal.coe_sub hst] at hω
  nlinarith

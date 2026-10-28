-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_no_deficit_prefix_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:29:31.483373+00:00
-- url     : https://prove2.me/submissions/fdfa94f0-39fc-4e4b-a855-c428e94b3ecb

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_history_zero_exponential_survival
import Mathlib.MeasureTheory.Measure.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
      X.drift * (s : ℝ) - X.X s ω = 0} =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  simpa only [mul_comm X.drift] using
    (AvramDividend.Classical.bv_actual_residual_history_zero_exponential_survival
      X hBV hFinite t)

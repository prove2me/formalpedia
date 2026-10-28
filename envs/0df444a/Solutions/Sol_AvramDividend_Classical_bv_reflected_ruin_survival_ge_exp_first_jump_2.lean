-- Prove2me | solution 2 for AvramDividend.Classical.bv_reflected_ruin_survival_ge_exp_first_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:35:12.151984+00:00
-- url     : https://prove2.me/submissions/e2f7284a-40b4-45c8-87fc-1854b134d9e2

import Theorems.Thm_AvramDividend_Classical_bv_zero_residual_prefix_before_reflected_ruin
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_history_zero_exponential_survival
import Mathlib.MeasureTheory.Measure.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Zero residual through time t implies genuine reflected survival through time t. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) ≤
      P.real {ω : Ω | (t : ℝ≥0∞) ≤ barrierRuinTime X 0 ω} := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hSub :
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
        (s : ℝ) * X.drift - X.X s ω = 0} ⊆
      {ω : Ω | (t : ℝ≥0∞) ≤ barrierRuinTime X 0 ω} := by
    intro ω hw
    exact bv_zero_residual_prefix_before_reflected_ruin
      X hStanding hBV ω t hw
  calc
    Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) =
      P.real {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
        (s : ℝ) * X.drift - X.X s ω = 0} :=
        (bv_actual_residual_history_zero_exponential_survival
          X hBV hFinite t).symm
    _ ≤ P.real {ω : Ω | (t : ℝ≥0∞) ≤ barrierRuinTime X 0 ω} :=
      measureReal_mono hSub

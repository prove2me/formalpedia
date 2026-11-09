-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_zero_barrier_survival_source_drift_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:45:08.9142+00:00
-- url     : https://prove2.me/submissions/6c88a02e-aaad-47b7-82a0-58166cea29a0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < barrierRuinTime X 0 ω →
      X.X T ω = (T : ℝ) * X.drift := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hreal :
      P.real {ω : Ω |
        (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
        0 < X.drift * (T : ℝ) - X.X T ω} = 0 :=
    bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
      X hBV hFinite T
  have hnull : P {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
      0 < X.drift * (T : ℝ) - X.X T ω} = 0 := by
    exact (measureReal_eq_zero_iff).mp hreal
  have hnot : ∀ᵐ ω ∂P,
      ¬ ((T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
        0 < X.drift * (T : ℝ) - X.X T ω) := by
    apply ae_iff.mpr
    simpa only [not_not] using hnull
  filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV T, hnot]
    with ω hle hbad
  intro hsurv
  by_contra hne
  have hstrict : X.X T ω < (T : ℝ) * X.drift :=
    lt_of_le_of_ne hle hne
  have hlt : 0 < X.drift * (T : ℝ) - X.X T ω := by
    nlinarith [hstrict]
  exact hbad ⟨hsurv, hlt⟩

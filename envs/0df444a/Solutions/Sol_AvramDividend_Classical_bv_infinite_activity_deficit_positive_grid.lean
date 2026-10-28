-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_deficit_positive_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:22:46.687952+00:00
-- url     : https://prove2.me/submissions/a057d6a8-619b-4414-a3ae-9fc318a4cd3b

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Infinite activity makes the actual drift deficit positive on any positive-time grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ n, 0 < grid n) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      0 < X.drift * (grid n : ℝ) - X.X (grid n) ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  apply (ae_all_iff).mpr
  intro n
  let T : ℝ≥0 := grid n
  have hZeroReal : P.real {ω : Ω |
      X.drift * (T : ℝ) - X.X T ω = 0} = 0 := by
    simpa only [T, mul_comm] using
      bv_infinite_activity_drift_deficit_zero_atom X hBV hνinf T (hgrid n)
  have hZeroNull : P {ω : Ω |
      X.drift * (T : ℝ) - X.X T ω = 0} = 0 :=
    (measureReal_eq_zero_iff).mp hZeroReal
  have hNotZero : ∀ᵐ ω ∂P,
      X.drift * (T : ℝ) - X.X T ω ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using hZeroNull
  filter_upwards
    [hNotZero, bv_actual_levy_drift_upper_ae_fixed_time X hBV T]
    with ω hne hUpper
  have hNonneg : 0 ≤ X.drift * (T : ℝ) - X.X T ω := by
    linarith
  have hPos := lt_of_le_of_ne hNonneg (Ne.symm hne)
  simpa only [T] using hPos

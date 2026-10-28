-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_zero_survival_deficit_zero_grid_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:01:21.481975+00:00
-- url     : https://prove2.me/submissions/91e30122-3c5d-47bd-82f5-a3892436bf24

import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A countable common null-set removal forces drift-only capital
on each surviving grid time, for the actual finite-activity process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((grid n : ℝ≥0) : ℝ≥0∞) < barrierRuinTime X 0 ω →
        X.X (grid n) ω = X.drift * (grid n : ℝ) := by
  letI : IsProbabilityMeasure P := X.isProbability
  apply (ae_all_iff).mpr
  intro n
  let T : ℝ≥0 := grid n
  let D : Ω → ℝ := fun ω => X.drift * (T : ℝ) - X.X T ω
  have hPosReal : P.real {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧ 0 < D ω} = 0 := by
    simpa only [D] using
      bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
        X hBV hFinite T
  have hPosNull : P {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧ 0 < D ω} = 0 :=
    (measureReal_eq_zero_iff).mp hPosReal
  have hNoPos : ∀ᵐ ω ∂P,
      ¬ ((T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧ 0 < D ω) := by
    apply ae_iff.mpr
    simpa only [not_not] using hPosNull
  filter_upwards
    [hNoPos, bv_actual_levy_drift_upper_ae_fixed_time X hBV T]
    with ω hNot hUpper
  intro hSurv
  have hNoDeficit : ¬ 0 < D ω := by
    intro hPos
    exact hNot ⟨hSurv, hPos⟩
  have hNonneg : 0 ≤ D ω := by
    dsimp [D]
    linarith
  have hZero : D ω = 0 := le_antisymm (le_of_not_gt hNoDeficit) hNonneg
  dsimp [D] at hZero
  linarith

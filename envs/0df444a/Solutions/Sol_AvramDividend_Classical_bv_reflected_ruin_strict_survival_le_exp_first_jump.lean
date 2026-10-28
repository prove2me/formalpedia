-- Prove2me | solution 1 for AvramDividend.Classical.bv_reflected_ruin_strict_survival_le_exp_first_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:02:06.087813+00:00
-- url     : https://prove2.me/submissions/265c7a46-4273-4bb9-9799-dbd462687ee5

import Theorems.Thm_AvramDividend_Classical_probability_survivor_bound_of_signed_null_exceptions
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Strict zero-barrier survival cannot exceed the first-negative-jump
exponential survival law in the actual BV finite-activity Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} ≤
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Set Ω := {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω}
  let D : Ω → ℝ := fun ω => X.drift * (t : ℝ) - X.X t ω
  have hPos : P.real {ω : Ω | ω ∈ A ∧ 0 < D ω} = 0 := by
    change P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
      0 < X.drift * (t : ℝ) - X.X t ω} = 0
    exact bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
      X hBV hFinite t
  have hAeNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω := by
    filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV t] with ω hx
    dsimp [D]
    linarith
  have hAeNotNeg : ∀ᵐ ω ∂P, ¬ D ω < 0 := by
    filter_upwards [hAeNonneg] with ω hx
    exact not_lt.mpr hx
  have hNegNull : P {ω : Ω | D ω < 0} = 0 := by
    simpa only [not_not] using (ae_iff.mp hAeNotNeg)
  have hNeg : P.real {ω : Ω | D ω < 0} = 0 := by
    simp [Measure.real, hNegNull]
  have hBound :=
    probability_survivor_bound_of_signed_null_exceptions P A D hPos hNeg
  calc
    P.real {ω : Ω | (t : ℝ≥0∞) < barrierRuinTime X 0 ω} =
      P.real A := rfl
    _ ≤ P.real {ω : Ω | D ω = 0} := hBound
    _ = Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
      simpa only [D, mul_comm] using
        bv_actual_residual_zero_atom_survival X hBV hFinite t

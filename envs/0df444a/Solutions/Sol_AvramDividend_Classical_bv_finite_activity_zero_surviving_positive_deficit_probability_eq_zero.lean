-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T15:51:54.563053+00:00
-- url     : https://prove2.me/submissions/8018c243-3621-415f-93be-4844d6cfb763

import Theorems.Thm_AvramDividend_Classical_bv_actual_surviving_positive_deficit_uniform_mesh_bound
import Theorems.Thm_AvramDividend_Classical_probability_uniform_mesh_bound_to_real
import Theorems.Thm_AvramDividend_Classical_uniform_nnreal_grid_spacing_real_eq_div
import Theorems.Thm_AvramDividend_Classical_positive_deficit_grid_event_rescale
import Theorems.Thm_AvramDividend_Classical_bv_actual_small_positive_deficit_probability_explicit_bound
import Theorems.Thm_AvramDividend_Classical_finite_activity_mesh_probability_bound_forces_zero
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
/-- Before zero-barrier ruin, a finite-activity BV Lévy path cannot
accumulate a positive negative-jump deficit with positive probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) :
    P.real {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
      0 < X.drift * (T : ℝ) - X.X T ω} = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let A : Set Ω := {ω : Ω |
    (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
    X.drift * (0 : ℝ) - X.X 0 ω < X.drift * (T : ℝ) - X.X T ω}
  have hBound : ∀ᶠ N : ℕ in atTop,
      P.real A ≤ Real.exp ((T : ℝ) * X.drift) *
        ((N : ℝ) * (Real.exp (-((T : ℝ) / (N : ℝ) *
          ∫ y in Iio (0 : ℝ), (1 - Real.exp ((N : ℝ) * y)) ∂X.ν)) -
          Real.exp (-((T : ℝ) / (N : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : 0 < N := hN
    obtain ⟨δ, hLength, hMeasure⟩ :=
      bv_actual_surviving_positive_deficit_uniform_mesh_bound X hBV T N hNpos
    let D : Ω → ℝ := fun ω => (δ : ℝ) * X.drift - X.X δ ω
    let B : Set Ω := {ω : Ω | 0 < X.drift * (δ : ℝ) - X.X δ ω ∧
      X.drift * (δ : ℝ) - X.X δ ω ≤ X.drift * (δ : ℝ)}
    let C : Set Ω := {ω : Ω |
      0 < D ω ∧ (N : ℝ) * D ω ≤ (T : ℝ) * X.drift}
    have hReal : P.real A ≤ (N : ℝ) * P.real B := by
      apply probability_uniform_mesh_bound_to_real P A B N
      simpa only [A, B] using hMeasure
    have hTime : (N : ℝ) * (δ : ℝ) = (T : ℝ) := by
      exact_mod_cast hLength
    have hDrift : (N : ℝ) * ((δ : ℝ) * X.drift) = (T : ℝ) * X.drift := by
      calc _ = ((N : ℝ) * (δ : ℝ)) * X.drift := by ring
           _ = (T : ℝ) * X.drift := by rw [hTime]
    have hBC : B = C := by
      calc
        B = {ω : Ω | 0 < D ω ∧ D ω ≤ (δ : ℝ) * X.drift} := by
          ext ω
          simp only [B, D, Set.mem_setOf_eq, mul_comm]
        _ = {ω : Ω | 0 < D ω ∧
                (N : ℝ) * D ω ≤ (N : ℝ) * ((δ : ℝ) * X.drift)} :=
          positive_deficit_grid_event_rescale D N hNpos ((δ : ℝ) * X.drift)
        _ = C := by rw [hDrift]
    have hSmall : P.real C ≤ Real.exp ((T : ℝ) * X.drift) *
        (Real.exp (-((δ : ℝ) * ∫ y in Iio (0 : ℝ),
          (1 - Real.exp ((N : ℝ) * y)) ∂X.ν)) -
         Real.exp (-((δ : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by
      exact bv_actual_small_positive_deficit_probability_explicit_bound
        X hBV hFinite δ N hN ((T : ℝ) * X.drift)
    have hSpacing :=
      uniform_nnreal_grid_spacing_real_eq_div T δ N hNpos hLength
    calc
      P.real A ≤ (N : ℝ) * P.real B := hReal
      _ = (N : ℝ) * P.real C := by rw [hBC]
      _ ≤ (N : ℝ) * (Real.exp ((T : ℝ) * X.drift) *
            (Real.exp (-((δ : ℝ) * ∫ y in Iio (0 : ℝ),
              (1 - Real.exp ((N : ℝ) * y)) ∂X.ν)) -
             Real.exp (-((δ : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)))) :=
        mul_le_mul_of_nonneg_left hSmall (by exact_mod_cast Nat.zero_le N)
      _ = _ := by rw [hSpacing]; ring
  have hZero := finite_activity_mesh_probability_bound_forces_zero
    X.ν hFinite (T : ℝ) ((T : ℝ) * X.drift) (P.real A)
    (NNReal.coe_nonneg T) (by exact measureReal_nonneg) hBound
  simpa [A, X.X_zero] using hZero

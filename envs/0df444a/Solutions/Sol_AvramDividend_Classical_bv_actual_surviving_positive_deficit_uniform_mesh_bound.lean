-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_surviving_positive_deficit_uniform_mesh_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T15:37:19.423057+00:00
-- url     : https://prove2.me/submissions/08a7fc88-2533-43c8-85ff-cb35cec31741

import Theorems.Thm_AvramDividend_Classical_nonnegative_uniform_time_grid_exists
import Theorems.Thm_AvramDividend_Classical_uniform_nnreal_grid_drift_arithmetic
import Theorems.Thm_AvramDividend_Classical_bv_survival_positive_deficit_measure_le_uniform_mesh_single_cell
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A genuine equal-duration mesh controls the surviving positive drift
deficit of an actual BV spectrally negative Lévy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    ∃ δ : ℝ≥0, (N : ℝ≥0) * δ = T ∧
      P {ω : Ω |
        (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
        X.drift * (0 : ℝ) - X.X 0 ω <
          X.drift * (T : ℝ) - X.X T ω} ≤
      (N : ℝ≥0∞) *
        P {ω : Ω |
          0 < X.drift * (δ : ℝ) - X.X δ ω ∧
          X.drift * (δ : ℝ) - X.X δ ω ≤
            X.drift * (δ : ℝ)} := by
  obtain ⟨ts, δ, hZero, hLast, hStep, hWithin, hSpacing, hLength⟩ :=
    nonnegative_uniform_time_grid_exists T N hN
  refine ⟨δ, hLength, ?_⟩
  obtain ⟨hDrift, _⟩ :=
    uniform_nnreal_grid_drift_arithmetic
      X.drift T δ N ts hStep hSpacing hLength
  have hMesh :
      ∀ k : ℕ, k < N →
        X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ)) ≤
          X.drift * (δ : ℝ) := by
    intro k hk
    exact le_of_eq (hDrift k hk)
  have hBound :=
    bv_survival_positive_deficit_measure_le_uniform_mesh_single_cell
      X hBV T N ts δ (X.drift * (δ : ℝ))
      hStep hWithin hMesh hSpacing
  simpa [hZero, hLast] using hBound

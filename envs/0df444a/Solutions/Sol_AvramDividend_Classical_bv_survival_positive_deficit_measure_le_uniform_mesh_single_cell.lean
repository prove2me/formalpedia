-- Prove2me | solution 1 for AvramDividend.Classical.bv_survival_positive_deficit_measure_le_uniform_mesh_single_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:14:15.668504+00:00
-- url     : https://prove2.me/submissions/ab549e72-2ea0-4b69-8f22-128676e48bf6

import Theorems.Thm_AvramDividend_Classical_bv_survival_positive_deficit_measure_le_grid_cell_bound
import Theorems.Thm_AvramDividend_Classical_actual_deficit_increment_uniform_grid_cell_measure_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A uniform grid reduces the strict-survival positive-deficit event to one actual-increment law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0)
    (δ : ℝ≥0) (b : ℝ)
    (hStep : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hMesh : ∀ k : ℕ, k < N →
      X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ)) ≤ b)
    (hSpacing : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) :
    P {ω : Ω |
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
      X.drift * (ts 0 : ℝ) - X.X (ts 0) ω <
        X.drift * (ts N : ℝ) - X.X (ts N) ω} ≤
      (N : ℝ≥0∞) *
        P {ω : Ω |
          0 < X.drift * (δ : ℝ) - X.X δ ω ∧
          X.drift * (δ : ℝ) - X.X δ ω ≤ b} := by
  have hCell :
      ∀ k : ℕ, k < N →
        P {ω : Ω |
          0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
            (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧
          (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
            (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b} ≤
        P {ω : Ω |
          0 < X.drift * (δ : ℝ) - X.X δ ω ∧
          X.drift * (δ : ℝ) - X.X δ ω ≤ b} :=
    actual_deficit_increment_uniform_grid_cell_measure_bound
      X N ts δ b (P {ω : Ω |
          0 < X.drift * (δ : ℝ) - X.X δ ω ∧
          X.drift * (δ : ℝ) - X.X δ ω ≤ b}) hStep hSpacing (le_refl _)
  exact bv_survival_positive_deficit_measure_le_grid_cell_bound
    X hBV T N ts b (P {ω : Ω |
          0 < X.drift * (δ : ℝ) - X.X δ ω ∧
          X.drift * (δ : ℝ) - X.X δ ω ≤ b})
    hStep hWithin hMesh hCell

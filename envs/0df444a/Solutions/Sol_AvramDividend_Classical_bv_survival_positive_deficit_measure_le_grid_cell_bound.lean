-- Prove2me | solution 1 for AvramDividend.Classical.bv_survival_positive_deficit_measure_le_grid_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:06:16.885493+00:00
-- url     : https://prove2.me/submissions/218d4f25-5920-4a7e-b703-bbb1cfde56f1

import Theorems.Thm_AvramDividend_Classical_bv_strict_survival_positive_deficit_grid_cell_ae
import Theorems.Thm_AvramDividend_Classical_finite_grid_event_measure_le_uniform_sum
import Mathlib.MeasureTheory.OuterMeasure.AE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A pathwise grid-cell inclusion and finite subadditivity give the
    measure bound for strictly surviving paths with positive net deficit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0)
    (b : ℝ) (u : ℝ≥0∞)
    (hStep : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hMesh : ∀ k : ℕ, k < N →
      X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ)) ≤ b)
    (hCell : ∀ k : ℕ, k < N →
      P {ω : Ω | 0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧ (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b} ≤ u) :
    P {ω : Ω |
        (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
        X.drift * (ts 0 : ℝ) - X.X (ts 0) ω < X.drift * (ts N : ℝ) - X.X (ts N) ω} ≤
      (N : ℝ≥0∞) * u := by
  have hPath :=
    bv_strict_survival_positive_deficit_grid_cell_ae
      X hBV T N ts b hStep hWithin hMesh
  have hSubset :
      {ω : Ω |
        (T : ℝ≥0∞) < barrierRuinTime X 0 ω ∧
        X.drift * (ts 0 : ℝ) - X.X (ts 0) ω < X.drift * (ts N : ℝ) - X.X (ts N) ω} ≤ᵐ[P]
      ⋃ k ∈ Finset.range N,
        {ω : Ω | 0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧ (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b} := by
    filter_upwards [hPath] with ω hω
    rintro ⟨hSurvive, hPositive⟩
    obtain ⟨k, hk, hSmall, hCap⟩ := hω hSurvive hPositive
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨Finset.mem_range.mpr hk, ⟨hSmall, hCap⟩⟩
  calc
    _ ≤ P (⋃ k ∈ Finset.range N,
          {ω : Ω | 0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧ (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b}) :=
        measure_mono_ae hSubset
    _ ≤ (N : ℝ≥0∞) * u :=
        finite_grid_event_measure_le_uniform_sum
          P (fun k => {ω : Ω | 0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧ (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) - (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b})
          N u hCell

-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_grid_exponential_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T08:01:48.455402+00:00
-- url     : https://prove2.me/submissions/ac5c8031-8a6a-4bcd-9dc4-fa83675ee60a

import Theorems.Thm_AvramDividend_Classical_nonnegative_deficit_mesh_integrability_package
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators

/-- Genuine BV drift-deficit increments give integrable mesh exponential moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (N : ℕ) (ts : ℕ → ℝ≥0) (D : ℕ → Ω → ℝ)
    (hD : ∀ k ω, D k ω =
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (a : ℝ) (ha : 0 < a)
    (hCellMeas : ∀ k : ℕ, k < N →
      AEStronglyMeasurable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) :
    (∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) ∧
    Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMono := bv_drift_deficit_ae_monotone_all_times X hBV
  have hIncrement : ∀ k : ℕ, k < N →
      ∀ᵐ ω ∂P, 0 ≤ D (k + 1) ω - D k ω := by
    intro k hk
    filter_upwards [hMono] with ω hω
    rw [hD (k + 1) ω, hD k ω]
    exact sub_nonneg.mpr (hω (hOrder k hk))
  exact nonnegative_deficit_mesh_integrability_package
    P N D a ha hIncrement hCellMeas

-- Prove2me | solution 1 for AvramDividend.Classical.bv_strict_survival_expected_deficit_uniform_mesh_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:58:12.78697+00:00
-- url     : https://prove2.me/submissions/a06ea4ff-7d49-4590-8cf1-e0bcea3ff43c

import Theorems.Thm_AvramDividend_Classical_bv_surviving_uniform_grid_deficit_caps
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_integral_indicator_capped_deficit_le_exp_partition
import Theorems.Thm_AvramDividend_Classical_bv_uniform_mesh_exp_gap_expected_sum
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Set Finset
open scoped NNReal ENNReal BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0) (δ : ℝ≥0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ k ω, D k ω =
      X.drift * (ts k : ℝ) - X.X (ts k) ω)
    (hOrder : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hStep : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (hStepReal : ∀ k : ℕ, k < N →
      (ts (k + 1) : ℝ) - (ts k : ℝ) = (δ : ℝ))
    (a : ℝ) (ha : 0 < a) (haEq : a = X.drift * (δ : ℝ))
    (hθ : 1 ≤ (1 / (2 * a) : ℝ))
    (hLeft : Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => D N ω - D 0 ω)) P)
    (hRight : Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P)
    (hCellInt : ∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) :
    (∫ ω, {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
      (fun ω => D N ω - D 0 ω) ω ∂P) ≤
      4 * a * (N : ℝ) *
        (1 - Real.exp (-((δ : ℝ) *
          ∫ y in Iio (0 : ℝ),
            (1 - Real.exp ((1 / (2 * a)) * y)) ∂X.ν))) := by
  have hNonneg : ∀ᵐ ω ∂P, ∀ k : ℕ, k < N → 0 ≤ D (k + 1) ω - D k ω := by
    filter_upwards [AvramDividend.Classical.bv_drift_deficit_ae_monotone_all_times X hBV] with ω hω k hk
    rw [hD, hD]
    have := hω (hOrder k hk)
    simp only at this
    linarith
  have hCap : ∀ ω ∈ {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}, ∀ k : ℕ, k < N →
      D (k + 1) ω - D k ω ≤ a := by
    intro ω hω k hk
    rw [hD, hD, haEq]
    exact AvramDividend.Classical.bv_surviving_uniform_grid_deficit_caps X T N ts δ hOrder hWithin
      hStepReal ω hω k hk
  have h1 := AvramDividend.Classical.integral_indicator_capped_deficit_le_exp_partition P _ D N a ha
    hNonneg hCap hLeft hRight
  refine h1.trans (le_of_eq ?_)
  have h2 := AvramDividend.Classical.bv_uniform_mesh_exp_gap_expected_sum X hBV N ts δ D hD hOrder hStep
    (1 / (2 * a)) hθ a hCellInt
  rw [← h2]
  congr 1
  funext ω
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 2
  ring

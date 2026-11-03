-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_bounded_predictable_grid_L2_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:58:22.691365+00:00
-- url     : https://prove2.me/submissions/c30d1750-ae88-45a9-99df-e32ce25652a0

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_predictable_grid_variance_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- A uniform bound on original predictable coefficient squares yields the
finite-grid source martingale L² energy bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ) (K : ℝ)
    (hOrder : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → s i + t i ≤ s j)
    (hWPast : ∀ i ∈ Finset.range n, Measurable[𝓕 (s i)] (W i))
    (hWI2 : ∀ i ∈ Finset.range n, Integrable (fun ω => (W i ω)^2) P)
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
    (hXI2 : ∀ i ∈ Finset.range n,
      Integrable (fun ω => (X.X (t i) ω)^2) P)
    (hEarlier : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → Integrable (fun ω =>
        (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))) * W j ω) P)
    (hPairI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))) * (W j ω * (X.X (s j + t j) ω - X.X (s j) ω -
          (∫ η, X.X (t j) η ∂P)))) P)
    (hWeightBound : ∀ i ∈ Finset.range n, ∀ ω, (W i ω)^2 ≤ K^2) :
    (∫ ω, (∑ i ∈ Finset.range n, (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))))^2 ∂P) ≤
      K^2 * ∑ i ∈ Finset.range n,
        (∫ ω, (X.X (t i) ω - (∫ η, X.X (t i) η ∂P))^2 ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hFactor :=
    avram_wave7_06_original_finite_predictable_grid_variance_factorisation
      X n s t W hOrder hWPast hWI2 hXI hXI2 hEarlier hPairI
  rw [hFactor]
  calc
    (∑ i ∈ Finset.range n,
      (∫ ω, (W i ω)^2 ∂P) *
        (∫ ω, (X.X (t i) ω - (∫ η, X.X (t i) η ∂P))^2 ∂P)) ≤
        ∑ i ∈ Finset.range n,
          K^2 * (∫ ω, (X.X (t i) ω -
            (∫ η, X.X (t i) η ∂P))^2 ∂P) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right
      · calc
          (∫ ω, (W i ω)^2 ∂P) ≤ (∫ _ : Ω, K^2 ∂P) := by
            apply integral_mono (hWI2 i hi) (integrable_const _)
            exact hWeightBound i hi
          _ = K^2 := by simp
      · exact integral_nonneg (fun ω => sq_nonneg _)
    _ = K^2 * ∑ i ∈ Finset.range n,
        (∫ ω, (X.X (t i) ω -
          (∫ η, X.X (t i) η ∂P))^2 ∂P) := by
      rw [Finset.mul_sum]

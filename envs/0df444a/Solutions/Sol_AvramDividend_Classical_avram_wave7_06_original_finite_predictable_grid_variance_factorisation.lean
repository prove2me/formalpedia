-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_variance_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:39:57.302025+00:00
-- url     : https://prove2.me/submissions/0c0551b9-87d1-4e36-9d9b-775c79e6739e

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_predictable_grid_centered_X_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact finite-grid stopped-predictable original scalar Lévy source energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ)
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
        (∫ η, X.X (t i) η ∂P))) *
        (W j ω * (X.X (s j + t j) ω - X.X (s j) ω -
        (∫ η, X.X (t j) η ∂P)))) P) :
    (∫ ω, (∑ i ∈ Finset.range n,
      (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))))^2 ∂P) =
      ∑ i ∈ Finset.range n,
        (∫ ω, (W i ω)^2 ∂P) *
          (∫ ω, (X.X (t i) ω - (∫ η, X.X (t i) η ∂P))^2 ∂P) := by
  rw [avram_wave7_06_original_finite_predictable_grid_centered_X_L2_isometry
    X n s t W hOrder hWPast hXI hEarlier hPairI]
  apply Finset.sum_congr rfl
  intro i hi
  exact
    avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry
      X (s i) (t i) (W i) (hWPast i hi) (hWI2 i hi)
        (hXI i hi) (hXI2 i hi)

-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_stopped_finite_grid_variance_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:51:22.33782+00:00
-- url     : https://prove2.me/submissions/14256199-ed93-455a-b50f-b238c67982d3

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_predictable_grid_variance_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Full original-filtration stopped predictable scalar finite-grid L² energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hOrder : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → s i + t i ≤ s j)
    (hWPast : ∀ i ∈ Finset.range n,
      Measurable[𝓕 (s i)] (fun ω => if i < τ ω then H i ω else 0))
    (hWI2 : ∀ i ∈ Finset.range n,
      Integrable (fun ω => (if i < τ ω then H i ω else 0)^2) P)
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
    (hXI2 : ∀ i ∈ Finset.range n,
      Integrable (fun ω => (X.X (t i) ω)^2) P)
    (hEarlier : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → Integrable (fun ω =>
        ((if i < τ ω then H i ω else 0) *
        (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))) *
          (if j < τ ω then H j ω else 0)) P)
    (hPairI : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => ((if i < τ ω then H i ω else 0) *
        (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))) *
        ((if j < τ ω then H j ω else 0) *
        (X.X (s j + t j) ω - X.X (s j) ω -
          (∫ η, X.X (t j) η ∂P)))) P) :
    (∫ ω, (∑ i ∈ Finset.range n, ((if i < τ ω then H i ω else 0) *
        (X.X (s i + t i) ω - X.X (s i) ω -
          (∫ η, X.X (t i) η ∂P))))^2 ∂P) =
      ∑ i ∈ Finset.range n,
        (∫ ω, (if i < τ ω then H i ω else 0)^2 ∂P) *
          (∫ ω, (X.X (t i) ω - (∫ η, X.X (t i) η ∂P))^2 ∂P) := by
  exact avram_wave7_06_original_finite_predictable_grid_variance_factorisation
    X n s t (fun i ω => if i < τ ω then H i ω else 0)
      hOrder hWPast hWI2 hXI hXI2 hEarlier hPairI

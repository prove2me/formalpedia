-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_centered_X_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:32:32.375398+00:00
-- url     : https://prove2.me/submissions/5c14294c-7e6d-478f-8d41-2c2df91bd6df

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite weighted centred sums on the genuine source filtration have mean
zero; suitable for stopped predictable simple coefficients on any finite grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hWPast : ∀ i ∈ Finset.range n, Measurable[𝓕 (s i)] (W i))
    (hWI : ∀ i ∈ Finset.range n, Integrable (W i) P)
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
    (hCellI : ∀ i ∈ Finset.range n, Integrable (fun ω =>
      W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P))) P) :
    (∫ ω, ∑ i ∈ Finset.range n,
      W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P)) ∂P) = 0 := by
  calc
    (∫ ω, ∑ i ∈ Finset.range n,
      W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P)) ∂P) =
        ∑ i ∈ Finset.range n, ∫ ω,
          W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
            (∫ η, X.X (t i) η ∂P)) ∂P := by
      exact integral_finset_sum (Finset.range n) hCellI
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact
        avram_wave7_06_original_predictable_weight_centered_future_increment_L1_orthogonal
          X (s i) (t i) (W i) (hWPast i hi) (hWI i hi) (hXI i hi)

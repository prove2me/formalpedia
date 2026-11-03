-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_finite_predictable_grid_centered_X_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:38:51.118488+00:00
-- url     : https://prove2.me/submissions/68322eb0-84ae-44d8-a12b-40fee5a18899

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_ordered_predictable_weighted_cells_covariance_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_pairwise_orthogonal_real_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original-filtration finite-grid weighted centred Lévy increments obey the
exact scalar L² isometry whenever all explicit pair products are integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (s t : ℕ → ℝ≥0) (W : ℕ → Ω → ℝ)
    (hOrder : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j → s i + t i ≤ s j)
    (hWPast : ∀ i ∈ Finset.range n, Measurable[𝓕 (s i)] (W i))
    (hXI : ∀ i ∈ Finset.range n, Integrable (X.X (t i)) P)
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
      ∑ i ∈ Finset.range n, ∫ ω, (W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
        (∫ η, X.X (t i) η ∂P)))^2 ∂P := by
  let A : ℕ → Ω → ℝ := fun i ω =>
    W i ω * (X.X (s i + t i) ω - X.X (s i) ω -
      (∫ η, X.X (t i) η ∂P))
  have hPair : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => A i ω * A j ω) P := hPairI
  have hOrth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → (∫ ω, A i ω * A j ω ∂P) = 0 := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact
        avram_wave7_06_original_ordered_predictable_weighted_cells_covariance_zero
          X (s i) (t i) (s j) (t j) (hOrder i hi j hj hlt)
          (W i) (W j) (hWPast i hi) (hWPast j hj) (hXI j hj)
          (hEarlier i hi j hj hlt)
    · have hz :=
        avram_wave7_06_original_ordered_predictable_weighted_cells_covariance_zero
          X (s j) (t j) (s i) (t i) (hOrder j hj i hi hgt)
          (W j) (W i) (hWPast j hj) (hWPast i hi) (hXI i hi)
          (hEarlier j hj i hi hgt)
      calc
        (∫ ω, A i ω * A j ω ∂P) =
            ∫ ω, A j ω * A i ω ∂P := by
          congr 1
          funext ω
          ring
        _ = 0 := hz
  exact avram_wave7_06_finite_pairwise_orthogonal_real_L2_isometry
    n A hPair hOrth

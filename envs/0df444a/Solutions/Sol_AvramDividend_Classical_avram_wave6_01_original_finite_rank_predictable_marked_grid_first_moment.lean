-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_finite_rank_predictable_marked_grid_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:57:25.515214+00:00
-- url     : https://prove2.me/submissions/9b40fb2d-3a50-4398-a4bb-f07f8e240f7f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_future_marked_increment_grid_weighted_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (I : Finset ι)
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ I, Measurable[𝓕 s] (H i))
    (B : ι → Set ℝ)
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (n : ℕ) (grid : ℕ → ℝ≥0) :
    (∫⁻ ω, ∑ i ∈ I, H i ω *
      ((((Finset.range n).filter (fun j =>
        (X.X (s + grid (j + 1)) ω - X.X s ω) -
          (X.X (s + grid j) ω - X.X s ω) ∈ B i)).card : ℝ≥0∞)) ∂P) =
    ∑ i ∈ I, (∫⁻ ω, H i ω ∂P) *
      (∫⁻ ω, ((((Finset.range n).filter (fun j =>
        (X.X (s + grid (j + 1)) ω - X.X s ω) -
          (X.X (s + grid j) ω - X.X s ω) ∈ B i)).card : ℝ≥0∞)) ∂P) := by
  classical
  have hXm : ∀ t, Measurable (X.X t) := fun t =>
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hMeasTerm (i : ι) (hi : i ∈ I) : Measurable (fun ω : Ω =>
      H i ω * ((((Finset.range n).filter (fun j =>
        (X.X (s + grid (j + 1)) ω - X.X s ω) -
          (X.X (s + grid j) ω - X.X s ω) ∈ B i)).card : ℝ≥0∞))) := by
    let p : ℕ → Ω → Prop := fun j ω =>
      (X.X (s + grid (j + 1)) ω - X.X s ω) -
        (X.X (s + grid j) ω - X.X s ω) ∈ B i
    have hp (j : ℕ) : MeasurableSet {ω : Ω | p j ω} := by
      exact (hB i hi).preimage
        (((hXm _).sub (hXm _)).sub ((hXm _).sub (hXm _)))
    have hSum : Measurable (fun ω : Ω =>
        ∑ j ∈ Finset.range n, if p j ω then (1 : ℕ) else 0) := by
      apply Finset.measurable_sum
      intro j hj
      exact Measurable.ite (hp j) measurable_const measurable_const
    have hEq :
        (fun ω : Ω => ((Finset.range n).filter (fun j => p j ω)).card) =
        (fun ω : Ω => ∑ j ∈ Finset.range n, if p j ω then (1 : ℕ) else 0) := by
      funext ω
      exact Finset.card_filter (fun j => p j ω) (Finset.range n)
    have hCount : Measurable (fun ω : Ω =>
        ((Finset.range n).filter (fun j => p j ω)).card) := by
      rw [hEq]
      exact hSum
    have hCast : Measurable (fun k : ℕ => (k : ℝ≥0∞)) :=
      measurable_of_countable _
    have hCountCast : Measurable (fun ω : Ω =>
        (((Finset.range n).filter (fun j => p j ω)).card : ℝ≥0∞)) :=
      hCast.comp hCount
    have hHglobal : Measurable (H i) :=
      (hH i hi).mono (𝓕.le s) le_rfl
    exact hHglobal.mul (by
      simpa only [p] using hCountCast)
  calc
    (∫⁻ ω, ∑ i ∈ I, H i ω *
      ((((Finset.range n).filter (fun j =>
        (X.X (s + grid (j + 1)) ω - X.X s ω) -
          (X.X (s + grid j) ω - X.X s ω) ∈ B i)).card : ℝ≥0∞)) ∂P) =
        ∑ i ∈ I, (∫⁻ ω, H i ω *
          ((((Finset.range n).filter (fun j =>
            (X.X (s + grid (j + 1)) ω - X.X s ω) -
              (X.X (s + grid j) ω - X.X s ω) ∈ B i)).card : ℝ≥0∞)) ∂P) := by
      apply MeasureTheory.lintegral_finset_sum
      intro i hi
      exact hMeasTerm i hi
    _ = ∑ i ∈ I, (∫⁻ ω, H i ω ∂P) *
      (∫⁻ ω, ((((Finset.range n).filter (fun j =>
        (X.X (s + grid (j + 1)) ω - X.X s ω) -
          (X.X (s + grid j) ω - X.X s ω) ∈ B i)).card : ℝ≥0∞)) ∂P) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact avram_wave6_01_original_future_marked_increment_grid_weighted_factor
        X s (H i) (hH i hi) (B i) (hB i hi) n grid

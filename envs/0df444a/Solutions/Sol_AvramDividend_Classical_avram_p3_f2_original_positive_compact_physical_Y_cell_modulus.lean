-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:40:41.690012+00:00
-- url     : https://prove2.me/submissions/5889bb84-91c9-4978-be28-70d30b504c43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_uniform_positive_compact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every positive compact original physical mesh inherits the true Y modulus. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (a b : ℝ≥0), 0 < a →
      let Y : ℝ≥0 → ℝ := fun t =>
        X.X t ω + ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (u : ℕ → ℝ≥0) (n : ℕ),
            (∀ i, i < n →
              u i ∈ Set.Icc a b ∧ u (i + 1) ∈ Set.Icc a b) →
            (∀ i, i < n → dist (u (i + 1)) (u i) < δ) →
            ∀ i, i < n →
              |Y (u (i + 1)) - Y (u i)| < ε := by
  filter_upwards
    [avram_p3_main_original_jump_removed_uniform_positive_compact X hBV]
    with ω hω
  intro a b ha Y ε hε
  rcases (Metric.uniformContinuousOn_iff.mp (hω a b ha)) ε hε with
    ⟨δ, hδ, hControl⟩
  refine ⟨δ, hδ, ?_⟩
  intro u n hCells hWidth i hi
  simpa only [Real.dist_eq] using
    hControl (u (i + 1)) (hCells i hi).2
      (u i) (hCells i hi).1 (hWidth i hi)

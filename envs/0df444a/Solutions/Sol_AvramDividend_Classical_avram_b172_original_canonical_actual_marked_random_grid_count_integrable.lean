-- Prove2me | solution 1 for AvramDividend.Classical.avram_b172_original_canonical_actual_marked_random_grid_count_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:14:45.4479+00:00
-- url     : https://prove2.me/submissions/021f4c53-d6fb-40f8-9cb3-c31affdfcc59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b165_original_true_bounded_random_monotone_marked_grid_count_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The canonical actual original physically jump-containing cells of any bounded random monotone stopped grid have a finite expected count under finite negative Levy activity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (grid : Ω → ℕ → ℝ≥0) (hMono : ∀ ω, Monotone (grid ω))
    (S : Finset ℕ)
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (∫⁻ ω, ((J ω).card : ℝ≥0∞) ∂P) < ⊤ := by
  intro J
  classical
  have hMarks : ∀ᵐ ω ∂P, ∀ i ∈ J ω, ∃ u : ℝ≥0,
      grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 :=
    Filter.Eventually.of_forall (fun ω i hi => (Finset.mem_filter.mp hi).2)
  have hRange : ∀ᵐ ω ∂P, ∀ i ∈ J ω, grid ω (i + 1) ≤ T :=
    Filter.Eventually.of_forall (fun ω i hi => hHorizon ω i (Finset.mem_filter.mp hi).1)
  exact avram_b165_original_true_bounded_random_monotone_marked_grid_count_integrable
    X hFinite n T hT grid hMono J hMarks hRange

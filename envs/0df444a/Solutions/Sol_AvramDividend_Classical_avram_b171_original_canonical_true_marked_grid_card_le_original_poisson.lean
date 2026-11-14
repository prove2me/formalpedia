-- Prove2me | solution 1 for AvramDividend.Classical.avram_b171_original_canonical_true_marked_grid_card_le_original_poisson
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:14:13.874707+00:00
-- url     : https://prove2.me/submissions/e6427669-de55-4802-8574-537051b8d9e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The canonical actual original jump-containing cells of a finite physical random monotone grid are bounded pathwise by the complete original negative Poisson source count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (S : Finset ℕ)
    (grid : Ω → ℕ → ℝ≥0)
    (hMono : ∀ ω, Monotone (grid ω))
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T) :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    ∀ ω, ((J ω).card : ℝ≥0∞) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) := by
  intro J
  classical
  intro ω
  have hMarks : ∀ i ∈ J ω, ∃ u : ℝ≥0,
      grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hRange : ∀ i ∈ J ω, grid ω (i + 1) ≤ T := by
    intro i hi
    exact hHorizon ω i (Finset.mem_filter.mp hi).1
  exact avram_b163_original_true_marked_monotone_grid_card_le_full_negative_poisson
    X ω T (grid ω) (hMono ω) (J ω) hMarks hRange

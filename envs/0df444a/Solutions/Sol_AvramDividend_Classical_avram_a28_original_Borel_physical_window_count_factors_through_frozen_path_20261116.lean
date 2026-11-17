-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_original_Borel_physical_window_count_factors_through_frozen_path_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:41:43.226661+00:00
-- url     : https://prove2.me/submissions/774e938e-241d-40f5-9b15-9aed8ced7285

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a28_cadlag_arbitrary_Borel_marked_halfopen_window_count_measurable_v2_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_physical_Borel_window_count_equals_frozen_path_encard_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hCad : ∀ ω : Ω,
      (∀ u : ℝ≥0, ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u) ∧
      (∀ u : ℝ≥0, 0 < u →
        ∃ l : ℝ, Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
          (𝓝[<] u) (𝓝 l))) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧ ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (min v T) ω) := by
  obtain ⟨F, hFm, hEq⟩ :=
    avram_a28_cadlag_arbitrary_Borel_marked_halfopen_window_count_measurable_v2_20261116
      s T B hB
  refine ⟨F, hFm, ?_⟩
  intro ω
  rw [avram_a28_original_physical_Borel_window_count_equals_frozen_path_encard_20261116
    X ω s T B hB]
  exact hEq _ (hCad ω).1 (hCad ω).2

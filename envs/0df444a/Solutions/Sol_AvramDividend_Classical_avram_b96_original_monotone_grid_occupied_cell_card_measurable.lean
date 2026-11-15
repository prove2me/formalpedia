-- Prove2me | solution 1 for AvramDividend.Classical.avram_b96_original_monotone_grid_occupied_cell_card_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:23:58.652009+00:00
-- url     : https://prove2.me/submissions/7ced85a7-d376-47c9-baee-bc4ad87e8d01

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The canonical source Poisson occupied-cell cardinal is measurable on a monotone grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    Measurable (fun ω : Ω =>
      (((Finset.range m).filter (fun i =>
        ((Measure.count.restrict {t : ℝ≥0 |
            0 < t ∧ X.X t ω -
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t, X.X t ω -
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc (u i) (u (i + 1)) ×ˢ (Set.univ : Set ℝ)) ≠ 0)).card : ℝ≥0∞)) := by
  classical
  have h := avram_bv_excess25_original_allnegative_occupied_grid_count_measurable
    X u hu m
  convert h using 1
  funext ω
  simp [Finset.card_filter, Nat.cast_sum]

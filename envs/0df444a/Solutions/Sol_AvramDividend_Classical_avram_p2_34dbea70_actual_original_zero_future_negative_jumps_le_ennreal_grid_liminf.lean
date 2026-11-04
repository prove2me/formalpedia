-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_original_zero_future_negative_jumps_le_ennreal_grid_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:16:07.148419+00:00
-- url     : https://prove2.me/submissions/3a2e864d-d84d-4bf3-9d65-1c95826da183

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENat ENNReal BigOperators

/-- The actual source's zero-future negative jumps satisfy the grid liminf. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (Y : ℝ≥0 → ℝ) (hY : Y = fun u => X.X u ω - X.X 0 ω) :
    ENat.toENNReal ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      Y u - Function.leftLim Y u ≠ 0 ∧
      Y u - Function.leftLim Y u ∈ Iic (-ε)}).encard ≤
      Filter.liminf (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
              Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
            then (1 : ℝ≥0∞) else 0)) atTop := by
  subst Y
  obtain ⟨hR, hL⟩ :=
    avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag X ω
  apply avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf
    (fun v : ℝ≥0 => X.X v ω - X.X 0 ω) _ T hT ε hε
  · intro u hu
    exact ⟨hu.1, hu.2.1⟩
  · intro u hu
    exact hL u hu.1
  · intro u hu
    exact hR u
  · intro u hu
    exact hu.2.2.2

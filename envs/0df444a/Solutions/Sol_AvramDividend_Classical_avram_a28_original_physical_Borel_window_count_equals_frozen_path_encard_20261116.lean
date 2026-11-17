-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_original_physical_Borel_window_count_equals_frozen_path_encard_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:55:12.446827+00:00
-- url     : https://prove2.me/submissions/6279b2ef-955f-4874-8ad5-356bd9b902b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_leftLim_before_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s T ×ˢ B) =
      ({u : ℝ≥0 | s < u ∧ u ≤ T ∧
        X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ≠ 0 ∧
        X.X (min u T) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u ∈ B}).encard := by
  classical
  let Y : ℝ≥0 → ℝ := fun v => X.X (min v T) ω
  have hJumpEq (u : ℝ≥0) (hu : 0 < u) (huT : u ≤ T) :
      Y u - Function.leftLim Y u =
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by
    dsimp [Y]
    rw [min_eq_left huT,
      avram_wave7_06_original_frozen_prefix_leftLim_before_stop X ω T u hu huT]
  have hSet :
      {u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B} =
      {u : ℝ≥0 | s < u ∧ u ≤ T ∧
        Y u - Function.leftLim Y u ≠ 0 ∧
        Y u - Function.leftLim Y u ∈ B} := by
    ext u
    constructor
    · rintro ⟨hu, hs, huT, hj, hm⟩
      have heq := hJumpEq u hu huT
      exact ⟨hs, huT, by simpa only [heq] using hj,
        by simpa only [heq] using hm⟩
    · rintro ⟨hs, huT, hj, hm⟩
      have hu : 0 < u := lt_of_le_of_lt bot_le hs
      have heq := hJumpEq u hu huT
      exact ⟨hu, hs, huT, by simpa only [heq] using hj,
        by simpa only [heq] using hm⟩
  calc
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s T ×ˢ B) =
      ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).encard :=
      avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
        X ω s T B hB
    _ = ({u : ℝ≥0 | s < u ∧ u ≤ T ∧
        Y u - Function.leftLim Y u ≠ 0 ∧
        Y u - Function.leftLim Y u ∈ B}).encard := by rw [hSet]

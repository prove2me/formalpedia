-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_original_intrinsic_negative_count_le_grid_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:33:35.613852+00:00
-- url     : https://prove2.me/submissions/9a53d0b9-c398-4cf1-9200-50c2ba9c21e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENat ENNReal BigOperators

/-- The actual original marked jump count is controlled by original increments. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ≤
      Filter.liminf (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          (if X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
              X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω < -ε / 2
            then (1 : ℝ≥0∞) else 0)) atTop := by
  let Y : ℝ≥0 → ℝ := fun u => X.X u ω - X.X 0 ω
  obtain ⟨hR, hL⟩ :=
    avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag X ω
  have hpath :
      ENat.toENNReal ({u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        Y u - Function.leftLim Y u ≠ 0 ∧
        Y u - Function.leftLim Y u ∈ Iic (-ε)}).encard ≤
      Filter.liminf (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
              Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
            then (1 : ℝ≥0∞) else 0)) atTop := by
    apply avram_p2_34dbea70_all_negative_path_jumps_le_ennreal_indicator_liminf
      Y _ T hT ε hε
    · intro u hu
      exact ⟨hu.1, hu.2.1⟩
    · intro u hu
      exact hL u hu.1
    · intro u hu
      exact hR u
    · intro u hu
      exact hu.2.2.2
  have htransport :=
    avram_wave5_01_actual_source_futurepath_marked_count_transport
      X ω 0 T (Iic (-ε)) measurableSet_Iic
  simp only [zero_add] at htransport
  have hbridge := htransport.le.trans hpath
  simpa only [zero_add, Y, sub_sub_sub_cancel_right] using hbridge

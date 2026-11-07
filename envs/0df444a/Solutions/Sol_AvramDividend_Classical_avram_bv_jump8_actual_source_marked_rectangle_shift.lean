-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_actual_source_marked_rectangle_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:05:09.91839+00:00
-- url     : https://prove2.me/submissions/c918871e-1fa1-46b5-b85c-c78932b1c365

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_interval_samepath_marked_count
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_shifted_increment_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_generic_measurable_mark_rectangle_encard
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
    (n : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
          Function.leftLim
            (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
          Function.leftLim
            (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u)))
      (Ioc 0 1 ×ˢ B) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (n : ℝ≥0) ((n : ℝ≥0) + 1) ×ˢ B) := by
  let Y : ℝ≥0 → ℝ := fun u =>
    X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω
  have hmap : Measurable (fun u : ℝ≥0 =>
      (u, Y u - Function.leftLim Y u)) :=
    avram_bv_jump8_original_shifted_increment_mark_map_measurable X ω n
  have hgeneric := avram_bv_jump8_generic_measurable_mark_rectangle_encard
    Y hmap 0 1 B hB
  have hsource := avram_wave7_01_original_arbitrary_interval_samepath_marked_count
    X ω (n : ℝ≥0) ((n : ℝ≥0) + 1) (by simp) B hB
  rw [hsource]
  simpa [Y, and_assoc, add_tsub_cancel_left] using hgeneric

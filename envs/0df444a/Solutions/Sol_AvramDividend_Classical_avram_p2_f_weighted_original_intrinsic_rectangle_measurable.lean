-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_rectangle_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:32:38.331441+00:00
-- url     : https://prove2.me/submissions/e815d367-6fbd-4c8f-867c-cea59d1a0c5b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Measurability of the literal source jump count follows from its genuine
shifted-future path representation, without any intensity hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) := by
  have hst : s ≤ s + T := le_add_of_nonneg_right (by positivity)
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s (s + T) hst B hB
  have hFuture : Measurable (fun ω : Ω =>
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) :=
    hF.comp
      (avram_wave7_01_original_shifted_future_path_coordinate_product_measurable X s)
  have hEq : (fun ω : Ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)) =
      (fun ω : Ω => F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) := by
    funext ω
    exact hExtract ω
  rw [hEq]
  exact hFuture

-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:45:50.449235+00:00
-- url     : https://prove2.me/submissions/3dee4691-41bb-4111-87b5-64546ca5faed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_Borel_physical_window_count_factors_through_frozen_path_20261116
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
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
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B)) := by
  obtain ⟨F, hF, hEq⟩ :=
    avram_a28_original_Borel_physical_window_count_factors_through_frozen_path_20261116
      X s T B hB (fun ω =>
        avram_wave7_06_original_frozen_prefix_cadlag_all_horizons X ω T)
  have hPath :=
    avram_bv_jump8_original_frozen_prefix_path_filtration_measurable X T
  have hComp : Measurable[𝓕 T] (fun ω : Ω =>
      F (fun v : ℝ≥0 => X.X (min v T) ω)) :=
    hF.comp hPath
  have heq : (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s T ×ˢ B)) =
      (fun ω : Ω => F (fun v : ℝ≥0 => X.X (min v T) ω)) := by
    funext ω
    exact hEq ω
  rw [heq]
  exact hComp

-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys75_original_zero_negative_mark_count_entire_source_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:52:59.310068+00:00
-- url     : https://prove2.me/submissions/f0ffdec2-a04e-44ab-bd21-90b119694eaa

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys74_original_no_physical_jumps_path_equals_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original intrinsic no-negative-mark paths equal the BV drift on the entire
horizon, on the original probability space and filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) →
      ∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift := by
  filter_upwards [avram_bvb_phys74_original_no_physical_jumps_path_equals_drift
    X hX hBV T] with ω hpath
  intro hZero
  apply hpath
  intro u hu huT
  have hnonneg := avram_bvb_phys73_original_zero_negative_mark_count_no_negative_jumps
    X ω T hZero u hu huT
  have hnonpos := avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu
  exact le_antisymm hnonpos hnonneg

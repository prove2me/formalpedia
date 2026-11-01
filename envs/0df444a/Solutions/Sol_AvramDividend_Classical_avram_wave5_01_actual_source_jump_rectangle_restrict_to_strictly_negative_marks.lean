-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:21:50.376924+00:00
-- url     : https://prove2.me/submissions/6d7d65d1-73c5-4682-a6f2-4ea0e3041171

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (B ∩ Iio (0 : ℝ))) := by
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω s t B hB,
    avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω s t (B ∩ Iio (0 : ℝ)) (hB.inter measurableSet_Iio)]
  congr 1
  congr 1
  ext u
  constructor
  · rintro ⟨hu0, hsu, hut, hj, hBmem⟩
    have hle : X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 :=
      avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu0
    have hlt : X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 :=
      lt_of_le_of_ne hle hj
    exact ⟨hu0, hsu, hut, hj, ⟨hBmem, hlt⟩⟩
  · rintro ⟨hu0, hsu, hut, hj, ⟨hBmem, _⟩⟩
    exact ⟨hu0, hsu, hut, hj, hBmem⟩

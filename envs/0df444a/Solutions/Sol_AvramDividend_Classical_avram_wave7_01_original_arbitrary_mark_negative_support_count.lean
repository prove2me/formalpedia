-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_arbitrary_mark_negative_support_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:23:06.218709+00:00
-- url     : https://prove2.me/submissions/b1a2282a-c4d5-483d-a09d-0152b2acbc55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-! The original path's nonzero marks lie in the strict negative half-line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
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
  have hBneg : MeasurableSet (B ∩ Iio (0 : ℝ)) :=
    hB.inter isOpen_Iio.measurableSet
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard X ω s t B hB,
    avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω s t (B ∩ Iio (0 : ℝ)) hBneg]
  apply congrArg (fun S : Set ℝ≥0 => (S.encard : ℝ≥0∞))
  ext u
  constructor
  · rintro ⟨hu, hsu, htu, hne, hmem⟩
    have hle := avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu
    have hlt :
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 := by
      rcases lt_or_eq_of_le hle with hstrict | heq
      · exact hstrict
      · exact False.elim (hne heq)
    exact ⟨hu, hsu, htu, hne, ⟨hmem, hlt⟩⟩
  · rintro ⟨hu, hsu, htu, hne, hmem⟩
    exact ⟨hu, hsu, htu, hne, hmem.1⟩

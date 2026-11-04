-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_nonnegative_mark_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:56:24.748091+00:00
-- url     : https://prove2.me/submissions/c900e587-a0f4-49a9-9f92-0bcdc2d10a6d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original source marks and original Levy measure give zero
mass to every measurable nonnegative mark test, including zero marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hNonneg : B ⊆ Ici (0 : ℝ)) :
    (∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = 0) ∧
      X.ν B = 0 := by
  have hEmpty : B ∩ Iio (0 : ℝ) = ∅ := by
    ext z
    constructor
    · intro hz
      have hzGe : 0 ≤ z := hNonneg hz.1
      have hzNeg : z < 0 := hz.2
      exact False.elim (not_lt_of_ge hzGe hzNeg)
    · intro hz
      exact False.elim ((Set.mem_empty_iff_false z).mp hz)
  constructor
  · intro ω
    rw [avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
      X ω s t B hB]
    simp [hEmpty]
  · rw [avram_wave7_01_original_levy_measure_arbitrary_mark_negative_restriction X B hB]
    simp [hEmpty]

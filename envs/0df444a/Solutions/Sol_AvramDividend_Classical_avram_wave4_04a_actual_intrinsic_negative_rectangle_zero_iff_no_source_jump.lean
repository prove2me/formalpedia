-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_negative_rectangle_zero_iff_no_source_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:18:37.952451+00:00
-- url     : https://prove2.me/submissions/b945540d-cd06-425c-8d01-203fe47bacc6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual source marked count is zero on the entire negative-mark
rectangle exactly when the original sample has no jumps in that time interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) = 0 ↔
      ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by
  classical
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω s t (Iio (0 : ℝ)) measurableSet_Iio]
  constructor
  · intro hZero u hu
    by_contra hJump
    have huPos : 0 < u :=
      lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) hu.1
    have huNeg :
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 :=
      lt_of_le_of_ne
        (avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u huPos)
        hJump
    have hMem :
        u ∈ {v : ℝ≥0 | 0 < v ∧ s < v ∧ v ≤ t ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0 ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ∈ Iio (0 : ℝ)} :=
      ⟨huPos, hu.1, hu.2, hJump, huNeg⟩
    have hEmpty :
        {v : ℝ≥0 | 0 < v ∧ s < v ∧ v ≤ t ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0 ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ∈ Iio (0 : ℝ)} =
        ∅ :=
      Set.encard_eq_zero.mp
        (ENat.toENNReal_inj.mp (by simpa using hZero))
    rw [hEmpty] at hMem
    simp at hMem
  · intro hNoJump
    have hEmpty :
        {v : ℝ≥0 | 0 < v ∧ s < v ∧ v ≤ t ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0 ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ∈ Iio (0 : ℝ)} =
        ∅ := by
      ext u
      constructor
      · intro hu
        exact False.elim (hu.2.2.2.1 (hNoJump u ⟨hu.2.1, hu.2.2.1⟩))
      · intro hu
        exact False.elim hu
    have hZeroENat :
        ({v : ℝ≥0 | 0 < v ∧ s < v ∧ v ≤ t ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0 ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ∈ Iio (0 : ℝ)}).encard =
        (0 : ℕ∞) :=
      Set.encard_eq_zero.mpr hEmpty
    simpa only [ENat.toENNReal_zero] using
      (ENat.toENNReal_inj.mpr hZeroENat)

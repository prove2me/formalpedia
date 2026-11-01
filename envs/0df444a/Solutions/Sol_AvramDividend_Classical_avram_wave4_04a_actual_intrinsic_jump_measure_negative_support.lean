-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:55:55.172077+00:00
-- url     : https://prove2.me/submissions/0faa1f4b-d5e0-450e-9913-b3f5fed8f980

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
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Ici (0 : ℝ)) = 0 := by
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    X ω s t (Ici (0 : ℝ)) measurableSet_Ici]
  have hempty :
      {u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Ici (0 : ℝ)}
        = ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hu
    rcases hu with ⟨hu0, _, _, hj0, hge⟩
    change 0 ≤ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u at hge
    have hle :=
      avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu0
    exact hj0 (le_antisymm hle hge)
  change (({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Ici (0 : ℝ)}).encard : ℝ≥0∞) = 0
  rw [hempty]
  simp

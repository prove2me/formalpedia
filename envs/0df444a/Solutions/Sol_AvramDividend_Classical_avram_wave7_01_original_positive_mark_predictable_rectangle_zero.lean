-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_positive_mark_predictable_rectangle_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:23:39.190122+00:00
-- url     : https://prove2.me/submissions/591879e9-8c9a-402b-8e2e-fc719e7df8fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-! Original intrinsic Lévy jump count gives zero mass to positive marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Ioi (0 : ℝ)) ∂P) =
    P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Ioi (0 : ℝ)) := by
  have hν : X.ν (Ioi (0 : ℝ)) = 0 := by
    have hsub : Ioi (0 : ℝ) ⊆ Ici (0 : ℝ) := by
      intro y hy
      exact le_of_lt (Set.mem_Ioi.mp hy)
    apply le_antisymm
    · calc
        X.ν (Ioi (0 : ℝ)) ≤ X.ν (Ici (0 : ℝ)) := measure_mono hsub
        _ = 0 := X.ν_Ici
    · exact bot_le
  have hCount (ω : Ω) :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Ioi (0 : ℝ)) = 0 := by
    rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
      X ω s t (Ioi (0 : ℝ)) isOpen_Ioi.measurableSet]
    have hEmpty :
        {u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Ioi (0 : ℝ)} = ∅ := by
      ext u
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rintro ⟨hu, -, -, -, hpos⟩
      have hnonpos := avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu
      exact (not_lt_of_ge hnonpos) hpos
    rw [hEmpty]
    simp
  simp only [hCount, lintegral_zero, hν, mul_zero]

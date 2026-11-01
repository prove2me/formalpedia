-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_nonnegative_mark_rectangle_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:00:40.339098+00:00
-- url     : https://prove2.me/submissions/819ce8a5-537f-4b0f-a899-615ada606f46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBnonneg : B ⊆ Ici (0 : ℝ)) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hν : X.ν B = 0 := by
    apply le_antisymm _ bot_le
    calc
      X.ν B ≤ X.ν (Ici (0 : ℝ)) := measure_mono hBnonneg
      _ = 0 := X.ν_Ici
  have hN (ω : Ω) :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) = 0 := by
    have hsub : Ioc s t ×ˢ B ⊆ Ioc s t ×ˢ Ici (0 : ℝ) := by
      intro p hp
      exact ⟨hp.1, hBnonneg hp.2⟩
    apply le_antisymm _ bot_le
    calc
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ≤
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Ici (0 : ℝ)) := measure_mono hsub
      _ = 0 := avram_wave4_04a_actual_intrinsic_jump_measure_negative_support X ω s t
  simp [hν, hN]

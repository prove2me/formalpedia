-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_actual_source_past_expected_mark_measure_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:21:52.482558+00:00
-- url     : https://prove2.me/submissions/cc848603-ee80-446b-b46c-f304a79bfbe9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_jump_mark_measure_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ ρ : Measure ℝ,
      ρ (Ici (0 : ℝ)) = 0 ∧
      ∀ B : Set ℝ, MeasurableSet B →
        ρ B = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P) := by
  classical
  obtain ⟨ρ, hρ⟩ :=
    avram_wave6_01_original_past_expected_jump_mark_measure_exists
      X s t hst A hA
  refine ⟨ρ, ?_, hρ⟩
  rw [hρ (Ici (0 : ℝ)) measurableSet_Ici]
  have hPoint (ω : Ω) :
      ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ Ici (0 : ℝ)) = 0 :=
    avram_wave4_04a_actual_intrinsic_jump_measure_negative_support
      X ω s t
  simp only [hPoint]
  simp

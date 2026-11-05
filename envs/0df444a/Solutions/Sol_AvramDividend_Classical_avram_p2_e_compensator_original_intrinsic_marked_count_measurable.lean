-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_intrinsic_marked_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:51:22.787612+00:00
-- url     : https://prove2.me/submissions/43d75491-620e-4b91-8adc-ff9b7b16b889

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal original-process intrinsic marked-jump count is globally measurable on the original probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) := by
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  have hX (u : ℝ≥0) : Measurable (X.X u) := by
    exact (X.adapted u).mono (𝓕.le u) le_rfl
  have hFuture :
      Measurable (fun ω : Ω =>
        fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) := by
    rw [measurable_pi_iff]
    intro v
    exact (hX (s + v)).sub (hX s)
  have hEq :
      (fun ω : Ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B)) =
      (fun ω : Ω =>
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) := by
    funext ω
    exact hExtract ω
  rw [hEq]
  exact hF.comp hFuture

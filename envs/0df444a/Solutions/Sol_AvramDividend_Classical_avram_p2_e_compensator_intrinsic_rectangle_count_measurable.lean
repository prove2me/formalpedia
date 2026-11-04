-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_intrinsic_rectangle_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:32:37.928355+00:00
-- url     : https://prove2.me/submissions/393e4507-4595-42a7-aea8-450dec5dd3ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every actual original-process intrinsic marked rectangle count is
measurable on the original sample space, including infinite counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun ω : Ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) := by
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  have hY : Measurable (fun ω : Ω =>
      fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) := by
    apply measurable_pi_iff.mpr
    intro v
    exact
      ((X.adapted (s + v)).mono (𝓕.le (s + v)) le_rfl).sub
        ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hEq :
      (fun ω : Ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) =
      (fun ω : Ω => F (fun v : ℝ≥0 =>
        X.X (s + v) ω - X.X s ω)) := by
    funext ω
    exact hExtract ω
  rw [hEq]
  exact hF.comp hY

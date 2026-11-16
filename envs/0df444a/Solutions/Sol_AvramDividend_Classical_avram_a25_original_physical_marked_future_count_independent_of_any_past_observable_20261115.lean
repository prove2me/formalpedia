-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_physical_marked_future_count_independent_of_any_past_observable_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:20:12.895004+00:00
-- url     : https://prove2.me/submissions/c2edef4a-1470-4a87-958d-c492e593a6cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
import Theorems.Thm_AvramDividend_Classical_levy_future_path_measurable_jump_extractor_indep_past_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original physical future marked count is independent of all past observables. -/
theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    IndepFun H (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨F, hF, hExtract, _⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
      X s (s + T)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ T from zero_le)) B hB
  have hInd :
      IndepFun H
        (fun ω => F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) P :=
    levy_future_path_measurable_jump_extractor_indep_past_ws01b
      X s H hH F hF
  have hEq :
      (fun ω : Ω => F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) =
      (fun ω : Ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s (s + T) ×ˢ B)) := by
    funext ω
    exact (hExtract ω).symm
  simpa only [hEq] using hInd

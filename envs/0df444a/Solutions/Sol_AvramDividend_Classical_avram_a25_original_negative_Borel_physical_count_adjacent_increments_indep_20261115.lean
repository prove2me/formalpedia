-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_negative_Borel_physical_count_adjacent_increments_indep_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:18:28.480901+00:00
-- url     : https://prove2.me/submissions/8d03f354-2d41-4c40-ab86-53cb5edadfc4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_borel_mark_count_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
import Theorems.Thm_AvramDividend_Classical_levy_future_path_measurable_jump_extractor_indep_past_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original marked counts before and after a deterministic time are independent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    IndepFun (fun ω => NX ω (Ioc 0 s ×ˢ B))
      (fun ω => NX ω (Ioc s (s + T) ×ˢ B)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hPast : Measurable[𝓕 s]
      (fun ω : Ω => NX ω (Ioc 0 s ×ˢ B)) := by
    simpa only [NX] using
      (avram_ja31_original_borel_mark_count_filtration_measurable X s B hB)
  obtain ⟨F, hF, hExtract, _⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
      X s (s + T) (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ T from zero_le))
      B hB
  have hInd :
      IndepFun (fun ω : Ω => NX ω (Ioc 0 s ×ˢ B))
        (fun ω => F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) P :=
    levy_future_path_measurable_jump_extractor_indep_past_ws01b
      X s (fun ω : Ω => NX ω (Ioc 0 s ×ˢ B)) hPast F hF
  have hEq :
      (fun ω : Ω => F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) =
      (fun ω : Ω => NX ω (Ioc s (s + T) ×ˢ B)) := by
    funext ω
    exact (hExtract ω).symm
  simpa only [hEq] using hInd

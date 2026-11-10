-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_gauss14_original_shifted_path_Borel_functional_indep_stopped_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:46:35.383208+00:00
-- url     : https://prove2.me/submissions/fa7c90f4-8d18-421b-987a-0790c29ff30c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every Borel functional of the original post-stop increment path is independent of the stopped past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (W : (ℝ≥0 → ℝ) → ℝ) (hW : Measurable W) :
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω => W (fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω))
        inferInstance) P := by
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  change Indep
    (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
    (MeasurableSpace.comap (W ∘ Y) inferInstance) P
  have hIndep : Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap Y inferInstance) P :=
    avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source X τ hτ
  have hY : Measurable[MeasurableSpace.comap Y inferInstance] Y :=
    measurable_iff_comap_le.mpr le_rfl
  have hWY : Measurable[MeasurableSpace.comap Y inferInstance] (W ∘ Y) :=
    hW.comp hY
  exact indep_of_indep_of_le_right hIndep hWY.comap_le

-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:38:07.433955+00:00
-- url     : https://prove2.me/submissions/1bf8c416-62b4-44f8-b5e4-2b81cd26dd8d

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedSigma_indep_shiftedPath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s}) :
    Indep
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace
      (MeasurableSpace.comap
        (fun ω : Ω => fun t : ℝ≥0 =>
          X.X (τ ω + t) ω - X.X (τ ω) ω)
        inferInstance) P := by
  obtain ⟨Y, hXY, hc, hσ, hν⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  simpa only [hXY] using
    (levy_finiteStopping_stoppedSigma_indep_shiftedPath Y τ hτ)

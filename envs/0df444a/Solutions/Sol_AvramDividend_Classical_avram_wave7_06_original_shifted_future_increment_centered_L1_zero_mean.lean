-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_shifted_future_increment_centered_L1_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:35:50.463143+00:00
-- url     : https://prove2.me/submissions/27859923-7c27-466c-a6c1-208c6424c1ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L1_integrable_equal_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Canonical source centred future increment has finite L¹ and zero expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (X.X t) P) :
    Integrable
      (fun ω => X.X (s + t) ω - X.X s ω -
        (∫ ω, X.X t ω ∂P)) P ∧
    (∫ ω, X.X (s + t) ω - X.X s ω -
      (∫ η, X.X t η ∂P) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hShiftInt, hShiftMean⟩ :=
    avram_wave7_06_original_future_increment_L1_integrable_equal_mean
      X s t hInt
  have hConst : Integrable
      (fun _ : Ω => (∫ ω, X.X t ω ∂P)) P :=
    integrable_const _
  refine ⟨hShiftInt.sub hConst, ?_⟩
  rw [integral_sub hShiftInt hConst, hShiftMean]
  simp

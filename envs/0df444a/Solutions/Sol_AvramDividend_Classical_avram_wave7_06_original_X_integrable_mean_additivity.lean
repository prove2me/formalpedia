-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_X_integrable_mean_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:09:59.914746+00:00
-- url     : https://prove2.me/submissions/5d02604e-14d8-4b33-a070-ca1accc5873a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L1_integrable_equal_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original-source Lévy mean additivity, with the actual future source
increment and all Bochner integrability justified. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hStart : Integrable (X.X s) P)
    (hFuture : Integrable (X.X t) P) :
    Integrable (X.X (s + t)) P ∧
    (∫ ω, X.X (s + t) ω ∂P) =
      (∫ ω, X.X s ω ∂P) + (∫ ω, X.X t ω ∂P) := by
  obtain ⟨hAInt, hAMean⟩ :=
    avram_wave7_06_original_future_increment_L1_integrable_equal_mean
      X s t hFuture
  have hSumInt : Integrable (fun ω =>
      (X.X (s + t) ω - X.X s ω) + X.X s ω) P :=
    hAInt.add hStart
  have hEndInt : Integrable (X.X (s + t)) P := by
    simpa only [sub_add_cancel] using hSumInt
  refine ⟨hEndInt, ?_⟩
  calc
    (∫ ω, X.X (s + t) ω ∂P) =
        ∫ ω, (X.X (s + t) ω - X.X s ω) + X.X s ω ∂P := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, X.X (s + t) ω - X.X s ω ∂P) +
        (∫ ω, X.X s ω ∂P) := integral_add hAInt hStart
    _ = (∫ ω, X.X s ω ∂P) +
        (∫ ω, X.X t ω ∂P) := by
      rw [hAMean]
      ring

-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_centered_future_L2_variance_stationarity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:45:23.531258+00:00
-- url     : https://prove2.me/submissions/2bcf9d22-8bcf-4213-87e5-adb0a89e94cd

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_centered_future_increment_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_centered_future_increment_square_identDistrib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original source centred future increments have exact second-moment stationarity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hFirst : Integrable (X.X t) P)
    (hSecond : Integrable (fun ω => (X.X t ω)^2) P) :
    Integrable (fun ω =>
      (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P))^2) P ∧
    (∫ ω, (X.X (s + t) ω - X.X s ω -
      (∫ η, X.X t η ∂P))^2 ∂P) =
      (∫ ω, (X.X t ω -
        (∫ η, X.X t η ∂P))^2 ∂P) := by
  have hSqInt :=
    avram_wave7_06_original_centered_future_increment_square_integrable
      X s t hFirst hSecond
  have hSqLaw :=
    avram_wave7_06_original_centered_future_increment_square_identDistrib
      X s t hFirst
  exact ⟨hSqInt, hSqLaw.integral_eq⟩

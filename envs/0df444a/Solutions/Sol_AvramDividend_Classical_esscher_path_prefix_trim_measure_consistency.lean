-- Prove2me | solution 1 for AvramDividend.Classical.esscher_path_prefix_trim_measure_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:58:27.532977+00:00
-- url     : https://prove2.me/submissions/fff697b0-4183-4913-b3ef-2cb3a89805e6

import Mathlib.MeasureTheory.Measure.Trim
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- All later Esscher path probabilities restrict to the same earlier filtration law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T) :
    @Measure.trim Ω (𝓕 s) mΩ
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (𝓕.le s) =
    @Measure.trim Ω (𝓕 s) mΩ
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
      (𝓕.le s) := by
  apply @Measure.ext Ω (𝓕 s)
  intro A hA
  rw [trim_measurableSet_eq (𝓕.le s) hA,
      trim_measurableSet_eq (𝓕.le s) hA]
  exact (chat04_esscher_finite_horizon_laws_consistent_on_past_events
    X θ hθ s T hsT A hA).symm

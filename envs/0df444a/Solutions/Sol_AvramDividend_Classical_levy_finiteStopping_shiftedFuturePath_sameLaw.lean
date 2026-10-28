-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_shiftedFuturePath_sameLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:43:48.983984+00:00
-- url     : https://prove2.me/submissions/b5e910fd-9249-4cc6-8193-7657b5873ae5

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The whole shifted post-stopping Lévy path has the same law as the initial path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    Measure.map
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) P =
      Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hUniv : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (Set.univ ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    simpa only [Set.univ_inter] using hτ s
  simpa only [Measure.restrict_univ, measure_univ, one_smul] using
    (levy_finiteStopping_restrictedFuturePath_mapLaw
      X τ (isStoppingTime_withTop_of_le_events τ hτ) Set.univ hUniv)

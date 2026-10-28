-- Prove2me | solution 1 for AvramDividend.Classical.progressive_of_pointwise_progressive_approximants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:15:54.035688+00:00
-- url     : https://prove2.me/submissions/9b9dcaf9-95d6-451f-9df4-aaa3a741dd9d

import Mathlib.Probability.Process.Adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- Progressive measurability is preserved by pointwise time-and-sample limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (U : ℕ → ℝ≥0 → Ω → ℝ)
    (u : ℝ≥0 → Ω → ℝ)
    (hU : ∀ n, ProgMeasurable 𝓕 (U n))
    (hpoint : ∀ t ω, Filter.Tendsto
      (fun n => U n t ω) Filter.atTop (nhds (u t ω))) :
    ProgMeasurable 𝓕 u := by
  apply isStronglyProgressive_of_tendsto hU
  exact tendsto_pi_nhds.mpr (fun t =>
    tendsto_pi_nhds.mpr (fun ω => hpoint t ω))

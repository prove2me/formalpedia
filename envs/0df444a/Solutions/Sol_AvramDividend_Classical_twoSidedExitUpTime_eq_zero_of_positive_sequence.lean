-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitUpTime_eq_zero_of_positive_sequence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:45:28.74753+00:00
-- url     : https://prove2.me/submissions/a55d8e63-92b8-4f77-98c8-8e7106018412

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.ENNReal.Lemmas

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s : ℕ → ℝ≥0)
    (hs : Tendsto s atTop (nhds 0))
    (hpos : ∀ n : ℕ, 0 < X.X (s n) ω) :
    twoSidedExitUpTime X 0 ω = 0 := by
  have h : ∀ n, twoSidedExitUpTime X 0 ω ≤ (s n : ℝ≥0∞) := by
    intro n
    have := twoSidedExitUpTime_le_observation_of_strict_exceedance X 0 0 ω (s n)
      (by simpa using hpos n)
    simpa using this
  have hs' : Tendsto (fun n => (s n : ℝ≥0∞)) atTop (nhds 0) := by
    have := (ENNReal.continuous_coe.tendsto 0).comp hs
    simpa [Function.comp_def] using this
  exact le_antisymm (ge_of_tendsto' hs' h) (zero_le)

-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_negative_sequence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:42:14.058993+00:00
-- url     : https://prove2.me/submissions/75f4b475-a00b-428a-943c-1311182337cd

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed
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
    (hneg : ∀ n : ℕ, X.X (s n) ω < 0) :
    twoSidedExitDownTime X 0 ω = 0 := by
  have h : ∀ n, twoSidedExitDownTime X 0 ω ≤ (s n : ℝ≥0∞) := by
    intro n
    have := twoSidedExitDownTime_le_of_strict_lower_gap_observed X 0 ω (s n) (by simpa using hneg n)
    simpa using this
  have hs' : Tendsto (fun n => (s n : ℝ≥0∞)) atTop (nhds 0) := by
    have := (ENNReal.continuous_coe.tendsto 0).comp hs
    simpa [Function.comp_def] using this
  exact le_antisymm (ge_of_tendsto' hs' h) (zero_le)

-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_near_threshold_crossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:41:17.313292+00:00
-- url     : https://prove2.me/submissions/923cb1a1-7925-47e9-99d6-c63235256309

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_sequence_at_threshold
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Near-zero strict crossings of any barrier imply zero first-passage time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω)
    (hnear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b) :
    twoSidedExitDownTime X b ω = 0 := by
  choose s hs hneg using fun n : ℕ => hnear ((n : ℝ≥0) + 1)⁻¹ (by positivity)
  apply twoSidedExitDownTime_eq_zero_of_sequence_at_threshold X b ω s _ hneg
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ≥0) + 1)⁻¹) atTop (𝓝 0) := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    rw [← NNReal.tendsto_coe]
    simpa using ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun n => zero_le) (fun n => (hs n).le)

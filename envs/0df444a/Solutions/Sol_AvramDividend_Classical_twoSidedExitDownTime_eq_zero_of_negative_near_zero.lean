-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_eq_zero_of_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:50:02.762423+00:00
-- url     : https://prove2.me/submissions/771161ca-42bd-43be-b7dc-0dfdf953762d

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_of_negative_sequence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hnear : ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    twoSidedExitDownTime X 0 ω = 0 := by
  choose s hs hneg using fun n : ℕ => hnear ((n : ℝ≥0) + 1)⁻¹ (by positivity)
  apply twoSidedExitDownTime_eq_zero_of_negative_sequence X ω s _ hneg
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ≥0) + 1)⁻¹) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    rw [← NNReal.tendsto_coe]
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun n => zero_le) (fun n => (hs n).le)

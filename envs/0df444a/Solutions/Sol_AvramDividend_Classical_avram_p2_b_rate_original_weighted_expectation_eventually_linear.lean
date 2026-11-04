-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_expectation_eventually_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:32:37.834449+00:00
-- url     : https://prove2.me/submissions/a490b5ed-66ef-4bc9-b850-ad18af6ebd9a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) ≤
          C * h := by
  let L : ℝ := ∫ y in Iio (0 : ℝ),
    (Real.exp (θ * y) - 1) ^ 4 ∂X.ν
  have hlim : Tendsto
      (fun h : ℝ =>
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds L) := by
    simpa only [zero_mul, Real.exp_zero, one_mul] using
      (avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
        X 0 θ (le_refl (0 : ℝ)) hθ.le)
  have hL : L < |L| + 1 := by
    have ha : L ≤ |L| := le_abs_self L
    linarith
  have hevent : ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0),
      (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h <
        |L| + 1 :=
    hlim.eventually (eventually_lt_nhds hL)
  refine ⟨|L| + 1, by positivity, ?_⟩
  filter_upwards [hevent, self_mem_nhdsWithin] with h hh hmem
  have hpos : 0 < h := hmem
  exact (div_le_iff₀ hpos).mp (le_of_lt hh)

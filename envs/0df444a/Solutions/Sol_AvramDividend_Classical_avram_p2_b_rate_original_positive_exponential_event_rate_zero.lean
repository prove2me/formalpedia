-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_positive_exponential_event_rate_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:06:22.653278+00:00
-- url     : https://prove2.me/submissions/79405ff2-e5d3-41c1-8b40-b6d467fed235

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_positive_event_all_k_real_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_eventual_all_power_tail_bounds_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 1 < R) :
    Tendsto (fun h : ℝ => ((P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal / h))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let C : ℝ := ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)
  have hpos : 0 < (R - 1) ^ 4 := pow_pos (by linarith) 4
  have hnonneg : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      0 ≤ ((P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal / h) := by
    have hp : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h := by
      change Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Ioi 0)
      exact self_mem_nhdsWithin
    filter_upwards [hp] with h hh
    positivity
  have hb (k : ℕ) : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      R ^ k * ((P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal / h) ≤ C / (R - 1) ^ 4 := by
    have hh :=
      AvramDividend.Classical.avram_p2_b_rate_original_positive_event_all_k_real_bound
        X hX θ R hθ hR k
    filter_upwards [hh] with h hbound
    apply (le_div_iff₀ hpos).2
    dsimp [C] at *
    nlinarith [hbound]
  exact
    AvramDividend.Classical.avram_p2_b_rate_eventual_all_power_tail_bounds_tendsto_zero
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (fun h : ℝ => ((P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal / h))
      R (C / (R - 1) ^ 4) hR hnonneg hb

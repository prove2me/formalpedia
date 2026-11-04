-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_increment_lintegral_markov_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:35:04.975147+00:00
-- url     : https://prove2.me/submissions/4a0af470-4e5b-4d0d-bc2b-a829382c54a7

import Mathlib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_fourth_weight_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y)
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ENNReal.ofReal ((1 - Real.exp (-θ * ε)) ^ 4) *
      μ {ω | Y ω ≤ -ε} ≤
    ∫⁻ ω, ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4) ∂μ := by
  let C : ℝ := (1 - Real.exp (-θ * ε)) ^ 4
  let w : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4)
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hsubset :
      {ω | Y ω ≤ -ε} ⊆ {ω | ENNReal.ofReal C ≤ w ω} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal
      (AvramDividend.Classical.avram_p2_b_rate_negative_band_fourth_weight_lower
        θ ε (Y ω) hθ hε hω)
  change ENNReal.ofReal C * μ {ω | Y ω ≤ -ε} ≤ ∫⁻ ω, w ω ∂μ
  calc
    ENNReal.ofReal C * μ {ω | Y ω ≤ -ε} ≤
        ENNReal.ofReal C * μ {ω | ENNReal.ofReal C ≤ w ω} := by
      gcongr
    _ ≤ ∫⁻ ω, w ω ∂μ := by
      exact MeasureTheory.mul_meas_ge_le_lintegral hw (ENNReal.ofReal C)
-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_positive_eventually_common_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:44:03.742428+00:00
-- url     : https://prove2.me/submissions/90943ac4-55ca-4a98-80b3-6fd489fe5202

import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_positive_increment_eventually_linear
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_all_moments_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_weighted_integral_moment_le_zero

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
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 1 < R) (k : ℕ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ENNReal.ofReal (R ^ k * (R - 1) ^ 4) *
        P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)} ≤
      ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := by
  have hzero : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) X.ν := by
    simpa using
      AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_moment_integrable
        X 0 θ le_rfl hθ
  have hk :=
    AvramDividend.Classical.avram_p2_b_rate_negative_weighted_all_moments_integrable
      X.ν θ hθ k hzero
  have hdom :=
    AvramDividend.Classical.avram_p2_b_rate_negative_weighted_integral_moment_le_zero
      X.ν θ hθ k hzero hk
  have hsmall :=
    AvramDividend.Classical.avram_p2_b_rate_original_positive_increment_eventually_linear
      X hX θ R hθ hR k
  have hp : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h := by
    change Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Ioi 0)
    exact self_mem_nhdsWithin
  filter_upwards [hsmall, hp] with h hh hpos
  calc
    _ ≤ ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y)) ^ k *
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := hh
    _ ≤ ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left
        (by linarith [hdom]) (le_of_lt hpos)

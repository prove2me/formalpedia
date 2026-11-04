-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_positive_increment_eventually_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:53:07.212375+00:00
-- url     : https://prove2.me/submissions/9b58e5c5-65ec-49fc-b8ba-4d9213b94c1d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_each_high_moment_eventually_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_positive_increment_weighted_markov

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
        ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := by
  have hE :=
    AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_bounded
      X k θ hθ
  have hp : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h := by
    change Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Ioi 0)
    exact self_mem_nhdsWithin
  filter_upwards [hE, hp] with h hratio hh
  have hInt :=
    AvramDividend.Classical.avram_p2_b_rate_original_weighted_integer_integrable
      X (Real.toNNReal h) k θ hθ
  have hMarkov :=
    AvramDividend.Classical.avram_p2_b_rate_positive_increment_weighted_markov
      P (X.X (Real.toNNReal h)) (hX _) θ R hR k hInt
  have hupper :
      (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
        (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) ≤
      h * ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1) := by
    have hh' := (div_lt_iff₀ hh).mp hratio
    linarith
  calc
    _ ≤ ENNReal.ofReal
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
          (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) := hMarkov
    _ ≤ ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) :=
      ENNReal.ofReal_le_ofReal hupper

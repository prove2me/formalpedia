-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_negative_band_eventually_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:56:55.521674+00:00
-- url     : https://prove2.me/submissions/8b176490-fe2d-4509-ab36-9a25c4f274ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_increment_lintegral_markov_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_fourth_weight_real_lintegral_identification

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
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ENNReal.ofReal ((1 - Real.exp (-θ * ε)) ^ 4) *
        P {ω | X.X (Real.toNNReal h) ω ≤ -ε} ≤
      ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := by
  have hE :=
    AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded
      X θ (le_of_lt hθ)
  have hp : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h := by
    change Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Ioi 0)
    exact self_mem_nhdsWithin
  filter_upwards [hE, hp] with h hratio hh
  have hInt :=
    AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_integrable
      X (Real.toNNReal h) θ (le_of_lt hθ)
  have hMarkov :=
    AvramDividend.Classical.avram_p2_b_rate_negative_increment_lintegral_markov_bound
      P (X.X (Real.toNNReal h)) (hX _) θ ε hθ hε
  have hReal :=
    AvramDividend.Classical.avram_p2_b_rate_fourth_weight_real_lintegral_identification
      P (X.X (Real.toNNReal h)) θ hInt
  have hupper :
      (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) ≤
        h * ((∫ y in Iio (0 : ℝ),
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1) := by
    have hh' := (div_lt_iff₀ hh).mp hratio
    nlinarith
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal
        ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P := hMarkov
    _ = ENNReal.ofReal
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) := hReal.symm
    _ ≤ ENNReal.ofReal (h *
        ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) :=
      ENNReal.ofReal_le_ofReal hupper

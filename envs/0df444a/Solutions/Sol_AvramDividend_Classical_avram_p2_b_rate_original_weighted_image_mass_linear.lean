-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_original_weighted_image_mass_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:02:49.933025+00:00
-- url     : https://prove2.me/submissions/33cd8824-d6e3-429f-8d3c-df89435dc907

import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded

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
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (((P.withDensity (fun ω =>
          ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω))) Set.univ) ≤
        ENNReal.ofReal (h *
          ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1)) := by
  have hb :=
    AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded
      X θ hθ
  filter_upwards [hb, self_mem_nhdsWithin] with h hh hpos
  have hp : 0 < h := hpos
  have hInt :=
    AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_integrable
      X (Real.toNNReal h) θ hθ
  have hn : ∀ᵐ ω ∂P,
      0 ≤ (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 :=
    Filter.Eventually.of_forall (fun ω => by positivity)
  have hm : Measurable (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω)) :=
    (Real.measurable_exp).comp (measurable_const.mul (hX _))
  have hmass :
      (((P.withDensity (fun ω =>
        ENNReal.ofReal ((Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
        (fun ω => Real.exp (θ * X.X (Real.toNNReal h) ω))) Set.univ) =
      ENNReal.ofReal
        (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) := by
    rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ]
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hn).symm
  rw [hmass]
  apply ENNReal.ofReal_le_ofReal
  have hlt :
      (∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) <
        ((∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1) * h :=
    (div_lt_iff₀ hp).mp hh
  nlinarith [hlt]

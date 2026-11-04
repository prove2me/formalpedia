-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_real_moment_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:04:47.342198+00:00
-- url     : https://prove2.me/submissions/7dfddd89-b9d9-4d56-ab9f-2f2b0d8c0e56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_tilt_lintegral_le
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_moment_formula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The kth ENNReal moment of the genuine negative Levy weighted image
is the ofReal of the integrable real tilted Levy generator test. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) =
    ENNReal.ofReal (∫ y in Iio (0 : ℝ),
      Real.exp ((k : ℝ) * y) * (Real.exp y - 1) ^ 4 ∂X.ν) := by
  let w : ℝ → ℝ≥0∞ :=
    fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4)
  let μ : Measure ℝ :=
    (((X.ν.restrict (Iio (0 : ℝ))).withDensity w).map Real.exp)
  haveI : IsFiniteMeasure μ :=
    avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite X
  have hm : μ Set.univ < ⊤ := measure_lt_top μ Set.univ
  have hbase :
      (∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal ((Real.exp y - 1) ^ 4) ∂X.ν) < ⊤ := by
    have heq : μ Set.univ =
        (∫⁻ y in Iio (0 : ℝ),
          ENNReal.ofReal ((Real.exp y - 1) ^ 4) ∂X.ν) := by
      change (((X.ν.restrict (Iio (0 : ℝ))).withDensity w).map
        Real.exp) Set.univ = _
      rw [Measure.map_apply Real.measurable_exp MeasurableSet.univ]
      simp only [Set.preimage_univ]
      rw [withDensity_apply w MeasurableSet.univ]
      simp [w]
    exact heq ▸ hm
  have ht :
      (∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal (Real.exp ((k : ℝ) * y) *
          (Real.exp y - 1) ^ 4) ∂X.ν) < ⊤ :=
    (avram_p2_negative_levy_fourth_weighted_tilt_lintegral_le
      X (k : ℝ) (by positivity)).trans_lt hbase
  have hf : Measurable (fun y : ℝ =>
      Real.exp ((k : ℝ) * y) * (Real.exp y - 1) ^ 4) := by
    fun_prop
  have hn : 0 ≤ᵐ[X.ν.restrict (Iio (0 : ℝ))]
      (fun y : ℝ => Real.exp ((k : ℝ) * y) *
        (Real.exp y - 1) ^ 4) := by
    filter_upwards [] with y
    positivity
  have hi : Integrable (fun y : ℝ =>
      Real.exp ((k : ℝ) * y) * (Real.exp y - 1) ^ 4)
      (X.ν.restrict (Iio (0 : ℝ))) :=
    (lintegral_ofReal_ne_top_iff_integrable
      hf.aestronglyMeasurable hn).mp (ne_top_of_lt ht)
  rw [avram_p2_negative_levy_fourth_weighted_exp_pushforward_moment_formula
    X k]
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  apply lintegral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
  rw [Real.exp_nat_mul]
  ac_rfl

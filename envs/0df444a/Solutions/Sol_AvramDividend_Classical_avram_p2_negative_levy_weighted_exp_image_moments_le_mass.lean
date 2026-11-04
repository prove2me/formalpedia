-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_image_moments_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:56:39.680173+00:00
-- url     : https://prove2.me/submissions/9687cae5-cd7d-4ec3-87a2-0390ea71455b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_compact_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every nonnegative polynomial moment of the actual finite weighted
negative Lévy image is bounded by its total mass: the image is on [0,1]. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) ≤
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ 0) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) := by
  let μ : Measure ℝ :=
    (((X.ν.restrict (Iio (0 : ℝ))).withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp)
  have hs : μ ((Icc (0 : ℝ) 1)ᶜ) = 0 :=
    avram_p2_negative_levy_weighted_exp_image_compact_support X
  have hae : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1 := by
    exact ae_iff.mpr hs
  change (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂μ) ≤
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ 0) ∂μ)
  apply lintegral_mono_ae
  filter_upwards [hae] with z hz
  have hpow : z ^ k ≤ 1 := by
    calc
      z ^ k ≤ 1 ^ k := by
        gcongr
        · exact hz.1
        · exact hz.2
      _ = 1 := one_pow k
  simpa only [pow_zero, ENNReal.ofReal_one] using
    (ENNReal.ofReal_le_ofReal hpow)

-- Prove2me | solution 1 for AvramDividend.Classical.original_purejump_UBV_negative_tail_mass_infinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:20:35.562024+00:00
-- url     : https://prove2.me/submissions/154d94df-9e60-4e87-a8fe-ee1e34c108c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation
import Theorems.Thm_AvramDividend_Classical_original_negative_tail_unweighted_layercake
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    (∫⁻ t in Ioi (0 : ℝ), X.ν (Iio (-t))) = ⊤ := by
  have hsmall := avram_p4_f4_original_purejump_ubv_infinite_variation
    X hBV hσ
  have hle : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) ≤
      (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂X.ν) :=
    by simpa only [setLIntegral_univ] using
      (lintegral_mono_set (subset_univ _))
  have htop : (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂X.ν) = ⊤ :=
    top_unique (by simpa only [hsmall] using hle)
  have hAE : ∀ᵐ y ∂X.ν, |y| = -y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp X.ν_Ici] with y hy
    have hy0 : y < 0 := lt_of_not_ge (by simpa only [mem_Ici] using hy)
    exact abs_of_neg hy0
  have hfull : (∫⁻ y : ℝ, ENNReal.ofReal (-y) ∂X.ν) = ⊤ := by
    rw [← lintegral_congr_ae (hAE.mono (fun _ h => congrArg ENNReal.ofReal h))]
    exact htop
  rw [← original_negative_tail_unweighted_layercake X.ν X.ν_Ici]
  exact hfull

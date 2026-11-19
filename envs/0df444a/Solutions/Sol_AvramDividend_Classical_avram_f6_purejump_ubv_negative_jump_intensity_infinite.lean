-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_purejump_ubv_negative_jump_intensity_infinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T16:13:46.437233+00:00
-- url     : https://prove2.me/submissions/f08afb35-6387-4f98-8b51-a1b6dfdc8f3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_purejump_ubv_infinite_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    X.ν (Iio (0 : ℝ)) = ⊤ := by
  have hinf :=
    avram_p4_f4_original_purejump_ubv_infinite_variation X hBV hσ
  have hBand : ∀ᵐ y ∂(X.ν.restrict (Ioo (-1 : ℝ) 0)),
      ENNReal.ofReal |y| ≤ (1 : ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hyabs : |y| ≤ 1 := by
      rw [abs_of_neg hy.2]
      linarith [hy.1]
    calc
      ENNReal.ofReal |y| ≤ ENNReal.ofReal (1 : ℝ) :=
        ENNReal.ofReal_le_ofReal hyabs
      _ = 1 := by norm_num
  have hI : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) ≤ X.ν (Ioo (-1 : ℝ) 0) := by
    calc
      _ ≤ ∫⁻ y in Ioo (-1 : ℝ) 0, (1 : ℝ≥0∞) ∂X.ν :=
        lintegral_mono_ae hBand
      _ = X.ν (Ioo (-1 : ℝ) 0) := by simp
  apply top_unique
  calc
    (⊤ : ℝ≥0∞) =
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) := hinf.symm
    _ ≤ X.ν (Ioo (-1 : ℝ) 0) := hI
    _ ≤ X.ν (Iio (0 : ℝ)) := measure_mono (by
      intro y hy
      exact hy.2)

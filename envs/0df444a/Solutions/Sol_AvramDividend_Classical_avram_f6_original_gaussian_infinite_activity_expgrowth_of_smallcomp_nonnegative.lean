-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_gaussian_infinite_activity_expgrowth_of_smallcomp_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:33:44.035256+00:00
-- url     : https://prove2.me/submissions/839a9ae9-1d77-458a-ad28-440ad0f345d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_infiniteactivity_full_negative_generator_lower_from_smallcomp
import Theorems.Thm_AvramDividend_Classical_avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : 0 < X.σ) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hSmallNonnegative : ∀ y : ℝ, 0 < y →
      0 ≤ ∫ z in Ioo (-1 : ℝ) 0,
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by
  have hPos : ∀ z : ℝ, 0 ≤ w z :=
    avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTop hw0 hwcont hwneg hwsmooth hwgrad
  have hRate : 0 ≤ (X.ν (Iic (-1 : ℝ))).toReal :=
    ENNReal.toReal_nonneg
  have hLower : ∀ y : ℝ, 0 < y →
      -(X.ν (Iic (-1 : ℝ))).toReal * w y ≤
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
    intro y hy
    have hyC : ENNReal.ofReal y < C := by simp [hTop]
    have hdy : 0 ≤ deriv w y := by
      have hh := hwgrad y hy hyC
      linarith
    have hTrue :=
      avram_f6_original_infiniteactivity_full_negative_generator_lower_from_smallcomp
        X w y hPos hdy (hwgen y hy hyC).1
    have hs := hSmallNonnegative y hy
    linarith
  exact avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
    X hσ q hq w C hTop hw0 hwcont hwneg hwsmooth
    hwgen (X.ν (Iic (-1 : ℝ))).toReal hRate hLower

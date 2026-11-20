-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:50:08.657732+00:00
-- url     : https://prove2.me/submissions/62361140-b14c-45a9-94e3-b69b558465a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finite_activity_generator_negative_jump_integral_floor
import Theorems.Thm_AvramDividend_Classical_avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_gbB36_interior_cap_positive_value_from_gradient
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (hνFin : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0))
    (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by
  have hσ : 0 < X.σ :=
    avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
      X hBV hνFin
  have hPos : ∀ y : ℝ, 0 ≤ w y := by
    intro y
    by_cases hy : 0 ≤ y
    · exact avram_gbB36_interior_cap_positive_value_from_gradient
        C w hw0 hwcont hwsmooth hwgrad y hy (by simp [hTop])
    · rw [hwneg y (lt_of_not_ge hy)]
  have hRate : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal := ENNReal.toReal_nonneg
  have hFloor : ∀ y : ℝ, 0 < y →
      -(X.ν (Iio (0 : ℝ))).toReal * w y ≤
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
    intro y hy
    have hyC : ENNReal.ofReal y < C := by simp [hTop]
    have hderiv : 0 ≤ deriv w y :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (hwgrad y hy hyC)
    exact avram_f6_original_finite_activity_generator_negative_jump_integral_floor
      X hνFin w hPos y hderiv (hwgen y hy hyC).1
  obtain ⟨θ, K, hθ, hK, hGrowth⟩ :=
    avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
      X hσ q hq w C hTop hw0 hwcont hwneg hwsmooth hwgen
      (X.ν (Iio (0 : ℝ))).toReal hRate hFloor
  exact ⟨θ, K, hθ, hK, fun y _ => hGrowth y⟩

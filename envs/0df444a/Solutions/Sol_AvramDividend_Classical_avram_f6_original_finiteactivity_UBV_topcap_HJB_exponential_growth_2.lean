-- Prove2me | solution 2 for AvramDividend.Classical.avram_f6_original_finiteactivity_UBV_topcap_HJB_exponential_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:54:10.000754+00:00
-- url     : https://prove2.me/submissions/8b4d910d-edef-40d3-88cf-3bd925e7fb75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection

import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_finite_jump_generator_lower
import Theorems.Thm_AvramDividend_Classical_avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
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
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y)  := by
  have hσ : 0 < X.σ :=
    avram_f6_original_finiteactivity_UBV_gaussian_sigma_positive
      X hBV hνFin
  have hwpos : ∀ y : ℝ, 0 ≤ w y := by
    intro y
    exact avram_ubv_top9_original_topcap_w_nonnegative_everywhere
      w C hTop hw0 hwcont hwneg hwsmooth hwgrad y
  let r : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hJumpLower : ∀ y : ℝ, 0 < y →
      -r * w y ≤
        ∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
    intro y hy
    have hCy : ENNReal.ofReal y < C := by simp [hTop]
    have hGen : X.GeneratorIntegrable w y := (hwgen y hy hCy).1
    have hDeriv : 0 ≤ deriv w y :=
      le_trans (by norm_num : (0 : ℝ) ≤ 1) (hwgrad y hy hCy)
    exact avram_mix_fin26_finite_jump_generator_lower
      X w y hνFin hGen (by intro t ht; exact hwpos t) hDeriv
  obtain ⟨θ, K, hθ, hK, hBound⟩ :=
    avram_f6_true_gaussian_jumplower_generator_HJB_exponential_growth
      X hσ q hq w C hTop hw0 hwcont hwneg
      hwsmooth hwgen r hr hJumpLower
  exact ⟨θ, K, hθ, hK, by intro y hy; exact hBound y⟩

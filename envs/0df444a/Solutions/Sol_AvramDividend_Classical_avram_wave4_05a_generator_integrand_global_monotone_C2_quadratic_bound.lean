-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05a_generator_integrand_global_monotone_C2_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:16:28.199845+00:00
-- url     : https://prove2.me/submissions/7b10872c-f1df-41ea-8342-ed615993d8e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_sq_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_generator_integrand_near_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_generator_integrand_far_monotone_quadratic_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hzero : ∀ z : ℝ, z < 0 → f z = 0)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 (y ^ 2) := by
  obtain ⟨r, Cnear, hr, hrle, hCnear, hnear⟩ :=
    AvramDividend.Classical.avram_wave4_05a_generator_integrand_near_C2_quadratic_bound X f a x hx hC2
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    AvramDividend.Classical.avram_wave4_05a_generator_integrand_far_monotone_quadratic_bound X f hzero hnonneg hmono x r hx.1 hr
  let C : ℝ := max Cnear Cfar
  have hC : 0 ≤ C := by
    dsimp [C]
    exact hCnear.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro y hy0
  by_cases hyr : y ≤ -r
  · have hkernel : 0 ≤ min 1 (y ^ 2) := by positivity
    calc
      ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖
          ≤ Cfar * min 1 (y ^ 2) := hfar y hy0 hyr
      _ ≤ C * min 1 (y ^ 2) :=
        mul_le_mul_of_nonneg_right (by
          dsimp [C]
          exact le_max_right _ _) hkernel
  · have hyr' : -r < y := lt_of_not_ge hyr
    have hyNear : y ∈ Ioo (-r) 0 := ⟨hyr', hy0⟩
    have hr1 : r ≤ 1 := hrle.trans (min_le_right x 1)
    have hym1 : -1 < y := by linarith
    have hy1 : y < 1 := by linarith
    have hprod : 0 < (1 - y) * (1 + y) :=
      mul_pos (by linarith) (by linarith)
    have hy2le : y ^ 2 ≤ 1 := by nlinarith
    have hmin : min 1 (y ^ 2) = y ^ 2 :=
      min_eq_right hy2le
    calc
      ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖
          ≤ Cnear * y ^ 2 := hnear y hyNear
      _ ≤ C * y ^ 2 :=
        mul_le_mul_of_nonneg_right (by
          dsimp [C]
          exact le_max_left _ _) (sq_nonneg y)
      _ = C * min 1 (y ^ 2) := by rw [hmin]

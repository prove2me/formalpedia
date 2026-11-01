-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05a_generator_integrand_far_monotone_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:06:52.93999+00:00
-- url     : https://prove2.me/submissions/57920d6d-2e5e-488b-80ed-66d4660912c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_sq_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
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
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 (y ^ 2) := by
  let B : ℝ := f x + |deriv f x|
  let m : ℝ := min 1 (r ^ 2)
  have hWx : 0 ≤ f x := hnonneg x
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min one_pos (sq_pos_of_pos hr)
  refine ⟨B / m, div_nonneg hB hm.le, ?_⟩
  intro y hy0 hyr
  have hWxy0 : 0 ≤ f (x + y) := by
    by_cases hxy : x + y < 0
    · rw [hzero (x + y) hxy]
    · exact hnonneg (x + y)
  have hWxy_le : f (x + y) ≤ f x := by
    by_cases hxy : x + y < 0
    · rw [hzero (x + y) hxy]
      exact hWx
    · exact hmono (by linarith)
  have hdiff : |f (x + y) - f x| ≤ f x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hWxy_le)]
    linarith
  have hcomp :
      |deriv f x * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤
        |deriv f x| := by
    by_cases hyI : y ∈ Ioo (-1 : ℝ) 1
    · have hind :
          (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 1 := by
        simp [hyI]
      rw [hind, mul_one, abs_mul]
      have hay : |y| ≤ 1 := (abs_lt.2 hyI).le
      exact mul_le_of_le_one_right (abs_nonneg _) hay
    · have hind :
          (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 0 := by
        simp [hyI]
      rw [hind, mul_zero, abs_zero]
      exact abs_nonneg _
  have hgenB :
      ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤ B := by
    rw [Real.norm_eq_abs]
    unfold SpectrallyNegativeLevy.generatorIntegrand
    calc
      |f (x + y) - f x -
          deriv f x * y * (Ioo (-1 : ℝ) 1).indicator 1 y|
          ≤ |f (x + y) - f x| +
              |deriv f x * y * (Ioo (-1 : ℝ) 1).indicator 1 y| := by
                exact abs_sub _ _
      _ ≤ f x + |deriv f x| := add_le_add hdiff hcomp
      _ = B := rfl
  have hry : r ≤ -y := by linarith
  have hsq : r ^ 2 ≤ y ^ 2 := by nlinarith
  have hmin : m ≤ min 1 (y ^ 2) := by
    dsimp [m]
    exact min_le_min le_rfl hsq
  calc
    ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤ B := hgenB
    _ = (B / m) * m := by field_simp
    _ ≤ (B / m) * min 1 (y ^ 2) :=
      mul_le_mul_of_nonneg_left hmin (div_nonneg hB hm.le)

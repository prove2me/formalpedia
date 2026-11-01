-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_generator_integrand_uniform_far_monotone_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:36:12.587797+00:00
-- url     : https://prove2.me/submissions/bcedfa19-c335-44ad-8765-850dcde22d7f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_bounded_on_compact_of_contDiff_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform far-jump bound for a nonnegative monotone test function with C² local regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z) (hmono : Monotone f)
    (a l u r : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a) (hr : 0 < r)
    (hC2 : ContDiffOn ℝ 2 f (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤
          C * min 1 (y ^ 2) := by
  have hsub : Icc l u ⊆ Ioo 0 a := by
    intro x hx
    exact ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 hu⟩
  obtain ⟨D, hD, hder⟩ :=
    deriv_bounded_on_compact_of_contDiff_two f a l u hlu hsub hC2
  let B : ℝ := f u + D
  let m : ℝ := min 1 (r ^ 2)
  have hfu : 0 ≤ f u := hnonneg u
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min one_pos (sq_pos_of_pos hr)
  refine ⟨B / m, div_nonneg hB hm.le, ?_⟩
  intro x hx y hy0 hyr
  have hWxy0 : 0 ≤ f (x + y) := hnonneg (x + y)
  have hWxy_le : f (x + y) ≤ f x := hmono (by linarith)
  have hWxu : f x ≤ f u := hmono hx.2
  have hdiff : |f (x + y) - f x| ≤ f u := by
    rw [abs_of_nonpos (sub_nonpos.mpr hWxy_le)]
    linarith
  have hcomp :
      |deriv f x * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤ D := by
    by_cases hyI : y ∈ Ioo (-1 : ℝ) 1
    · have hind :
          (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 1 := by
        simp [hyI]
      rw [hind, mul_one, abs_mul]
      have hay : |y| ≤ 1 := (abs_lt.2 hyI).le
      exact (mul_le_of_le_one_right (abs_nonneg _) hay).trans (hder x hx)
    · have hind :
          (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 0 := by
        simp [hyI]
      rw [hind, mul_zero, abs_zero]
      exact hD
  have hgenB :
      ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤ B := by
    rw [Real.norm_eq_abs]
    unfold SpectrallyNegativeLevy.generatorIntegrand
    calc
      |f (x + y) - f x -
        deriv f x * y * (Ioo (-1 : ℝ) 1).indicator 1 y|
          ≤ |f (x + y) - f x| +
              |deriv f x * y * (Ioo (-1 : ℝ) 1).indicator 1 y| :=
                abs_sub _ _
      _ ≤ f u + D := add_le_add hdiff hcomp
      _ = B := rfl
  have hry : r ≤ -y := by linarith
  have hsq : r ^ 2 ≤ y ^ 2 := by
    nlinarith
  have hmin : m ≤ min 1 (y ^ 2) := by
    dsimp [m]
    exact min_le_min le_rfl hsq
  calc
    ‖SpectrallyNegativeLevy.generatorIntegrand f x y‖ ≤ B := hgenB
    _ = (B / m) * m := by field_simp
    _ ≤ (B / m) * min 1 (y ^ 2) :=
      mul_le_mul_of_nonneg_left hmin (div_nonneg hB hm.le)

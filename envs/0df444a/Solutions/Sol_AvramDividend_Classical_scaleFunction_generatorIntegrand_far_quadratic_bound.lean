-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_far_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T07:03:05.722462+00:00
-- url     : https://prove2.me/submissions/db8776a9-c7cd-49ba-a177-b6b12f872603

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x r : ℝ)
    (hx : 0 ≤ x) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : ℝ, y ≤ -r →
        |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤
          C * min 1 (y ^ 2) := by
  have hWx : 0 ≤ W x := hW.2.1 x hx
  let B : ℝ := W x + |deriv W x|
  let m : ℝ := min 1 (r ^ 2)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min zero_lt_one hr2
  refine ⟨B / m, div_nonneg hB hm.le, ?_⟩
  intro y hyr
  have hyneg : y < 0 := by linarith
  have hyx : x + y ≤ x := by linarith
  have hWxy0 : 0 ≤ W (x + y) := by
    by_cases hxy : x + y < 0
    · rw [hW.1 (x + y) hxy]
    · exact hW.2.1 (x + y) (le_of_not_gt hxy)
  have hWxy_le : W (x + y) ≤ W x := by
    by_cases hxy : x + y < 0
    · rw [hW.1 (x + y) hxy]
      exact hWx
    · exact hW.2.2.2.1
        (show x + y ∈ Ici (0 : ℝ) by exact le_of_not_gt hxy)
        (show x ∈ Ici (0 : ℝ) by exact hx) hyx
  have hdiff : |W (x + y) - W x| ≤ W x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hWxy_le)]
    linarith
  have hcomp :
      |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤
        |deriv W x| := by
    by_cases hyI : y ∈ Ioo (-1 : ℝ) 1
    · have hind :
          (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 1 := by
        simp [hyI]
      rw [hind, mul_one, abs_mul]
      have hay : |y| ≤ 1 := abs_le.2 ⟨le_of_lt hyI.1, le_of_lt hyI.2⟩
      exact mul_le_of_le_one_right (abs_nonneg (deriv W x)) hay
    · have hind :
          (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y = 0 := by
        simp [hyI]
      rw [hind, mul_zero, abs_zero]
      exact abs_nonneg _
  have hnum :
      |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤ B := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    calc
      |W (x + y) - W x -
          deriv W x * y * (Ioo (-1 : ℝ) 1).indicator 1 y|
          ≤ |W (x + y) - W x| +
            |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator 1 y| := abs_sub _ _
      _ ≤ W x + |deriv W x| := add_le_add hdiff hcomp
      _ = B := by rfl
  have hyrabs : r ≤ |y| := by
    rw [abs_of_neg hyneg]
    linarith
  have hrsq : r ^ 2 ≤ y ^ 2 := by
    nlinarith [sq_nonneg (|y| - r), sq_abs y]
  have hmle : m ≤ min 1 (y ^ 2) := by
    dsimp [m]
    exact min_le_min le_rfl hrsq
  calc
    |SpectrallyNegativeLevy.generatorIntegrand W x y| ≤ B := hnum
    _ = (B / m) * m := by field_simp
    _ ≤ (B / m) * min 1 (y ^ 2) :=
      mul_le_mul_of_nonneg_left hmle (div_nonneg hB hm.le)

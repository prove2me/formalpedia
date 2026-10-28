-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_uniform_far_jump_linear_bound_on_compact_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:49:34.881418+00:00
-- url     : https://prove2.me/submissions/756d3d07-d819-4f3c-a0c0-a7ade06f6c60

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_bounds_of_nonpositive
import Theorems.Thm_AvramDividend_Classical_deriv_bounded_on_compact_of_contDiff_one
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- C1 regularity gives a uniform first-order jump bound away from zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u r : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a) (hr : 0 < r)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 |y| := by
  have hsub : Icc l u ⊆ Ioo 0 a := by
    intro x hx
    exact ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 hu⟩
  obtain ⟨D, hD, hder⟩ :=
    deriv_bounded_on_compact_of_contDiff_one W a l u hlu hsub hC1
  let B : ℝ := W u + D
  let m : ℝ := min 1 r
  have hu0 : 0 ≤ u := le_of_lt (hl.trans hlu)
  have hWu : 0 ≤ W u := hW.2.1 u hu0
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min one_pos hr
  refine ⟨B / m, div_nonneg hB hm.le, ?_⟩
  intro x hx y hy0 hyr
  have hx0 : 0 ≤ x := le_of_lt (lt_of_lt_of_le hl hx.1)
  have hs := scaleFunction_shift_bounds_of_nonpositive
    X q W hW x y hx0 (le_of_lt hy0)
  have hWxu : W x ≤ W u := hW.2.2.2.1 hx0 hu0 hx.2
  have hdiff : |W (x + y) - W x| ≤ W u := by
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith [hs.1]
  have hcomp :
      |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator 1 y| ≤ D := by
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
      ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤ B := by
    rw [Real.norm_eq_abs]
    unfold SpectrallyNegativeLevy.generatorIntegrand
    calc
      |W (x + y) - W x -
        deriv W x * y * (Ioo (-1 : ℝ) 1).indicator 1 y|
          ≤ |W (x + y) - W x| +
              |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator 1 y| :=
                abs_sub _ _
      _ ≤ W u + D := add_le_add hdiff hcomp
      _ = B := rfl
  have hyabs : r ≤ |y| := by
    rw [abs_of_neg hy0]
    linarith
  have hmin : m ≤ min 1 |y| := by
    dsimp [m]
    exact min_le_min le_rfl hyabs
  calc
    ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤ B := hgenB
    _ = (B / m) * m := by field_simp
    _ ≤ (B / m) * min 1 |y| :=
      mul_le_mul_of_nonneg_left hmin (div_nonneg hB hm.le)

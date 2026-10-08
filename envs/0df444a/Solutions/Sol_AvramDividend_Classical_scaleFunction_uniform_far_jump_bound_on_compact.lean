-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_uniform_far_jump_bound_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:36:16.182368+00:00
-- url     : https://prove2.me/submissions/166ec550-b62a-493b-9b1e-66d20459fa71

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

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u r : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a) (hr : 0 < r)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 (y ^ 2) := by
  have hsub : Icc l u ⊆ Ioo 0 a := by
    intro x hx
    exact ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 hu⟩
  obtain ⟨D, hD, hder⟩ :=
    deriv_bounded_on_compact_of_contDiff_two W a l u hlu hsub hC2
  let B : ℝ := W u + D
  let m : ℝ := min 1 (r ^ 2)
  have hu0 : 0 ≤ u := le_of_lt (hl.trans hlu)
  have hWu : 0 ≤ W u := hW.2.1 u hu0
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min one_pos (sq_pos_of_pos hr)
  refine ⟨B / m, div_nonneg hB hm.le, ?_⟩
  intro x hx y hy0 hyr
  have hx0 : 0 ≤ x := le_of_lt (lt_of_lt_of_le hl hx.1)
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hWxy0 : 0 ≤ W (x + y) := by
    by_cases hxy : x + y < 0
    · rw [hW.1 (x + y) hxy]
    · exact hW.2.1 (x + y) (le_of_not_gt hxy)
  have hWxy_le : W (x + y) ≤ W x := by
    by_cases hxy : x + y < 0
    · rw [hW.1 (x + y) hxy]
      exact hWx
    · exact hW.2.2.2.1 (le_of_not_gt hxy) hx0 (by linarith)
  have hWxu : W x ≤ W u := hW.2.2.2.1 hx0 hu0 hx.2
  have hdiff : |W (x + y) - W x| ≤ W u := by
    rw [abs_of_nonpos (sub_nonpos.mpr hWxy_le)]
    linarith
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
  have hry : r ≤ -y := by linarith
  have hsq : r ^ 2 ≤ y ^ 2 := by
    nlinarith
  have hmin : m ≤ min 1 (y ^ 2) := by
    dsimp [m]
    exact min_le_min le_rfl hsq
  calc
    ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤ B := hgenB
    _ = (B / m) * m := by field_simp
    _ ≤ (B / m) * min 1 (y ^ 2) :=
      mul_le_mul_of_nonneg_left hmin (div_nonneg hB hm.le)

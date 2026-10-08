-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrable_of_contDiff_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:30:00.720403+00:00
-- url     : https://prove2.me/submissions/3c2e2d5c-b02a-47a5-b57f-c4e2824fe979
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_bounds_of_nonpositive
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_contDiffOn_two_linear_remainder_isBigO
import Theorems.Thm_AvramDividend_Classical_integrableOn_Iio_zero_of_isBigO_sq_of_bound


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    X.GeneratorIntegrable W x := by
  have hx0 : 0 ≤ x := hx.1.le
  have hWx : 0 ≤ W x := hW.2.1 x hx0
  have hWmeas : Measurable W :=
    (scaleFunction_monotone X q W hW).measurable
  have hshiftmeas : Measurable (fun y : ℝ => W (x + y)) := by
    exact hWmeas.comp (by fun_prop)
  have hcompmeas :
      Measurable
        (fun y : ℝ =>
          deriv W x * y * (Ioo (-1 : ℝ) 1).indicator 1 y) := by
    have hlin : Measurable (fun y : ℝ => deriv W x * y) :=
      measurable_const.mul measurable_id
    have hind :
        Measurable ((Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
      measurable_const.indicator measurableSet_Ioo
    exact hlin.mul hind
  have hF :
      AEStronglyMeasurable
        (SpectrallyNegativeLevy.generatorIntegrand W x) X.ν := by
    apply Measurable.aestronglyMeasurable
    unfold SpectrallyNegativeLevy.generatorIntegrand
    exact (hshiftmeas.sub measurable_const).sub hcompmeas
  have hrem :=
    contDiffOn_two_linear_remainder_isBigO W a x hx hC2
  have hI : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hEq :
      (fun y : ℝ => W (x + y) - W x - deriv W x * y) =ᶠ[𝓝 0]
        SpectrallyNegativeLevy.generatorIntegrand W x := by
    filter_upwards [hI] with y hy
    simp [SpectrallyNegativeLevy.generatorIntegrand, hy]
  have hsmall :
      SpectrallyNegativeLevy.generatorIntegrand W x =O[𝓝 0]
        (fun y : ℝ => y ^ 2) :=
    hrem.congr' hEq (Filter.EventuallyEq.rfl)
  let B : ℝ := W x + |deriv W x|
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg hWx (abs_nonneg _)
  have hbound :
      ∀ y : ℝ, y < 0 →
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤ B := by
    intro y hy
    have hshift :=
      scaleFunction_shift_bounds_of_nonpositive
        X q W hW x y hx0 hy.le
    have hdiff :
        ‖W (x + y) - W x‖ ≤ W x := by
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hshift.2)]
      linarith [hshift.1]
    have hcomp :
        ‖deriv W x * y * (Ioo (-1 : ℝ) 1).indicator 1 y‖
          ≤ |deriv W x| := by
      by_cases hyI : y ∈ Ioo (-1 : ℝ) 1
      · rw [indicator_of_mem hyI]
        simp only [Pi.one_apply, mul_one, Real.norm_eq_abs, abs_mul]
        have hyabs : |y| ≤ 1 :=
          abs_le.2 ⟨le_of_lt hyI.1, le_of_lt hyI.2⟩
        calc
          |deriv W x| * |y| ≤ |deriv W x| * 1 :=
            mul_le_mul_of_nonneg_left hyabs (abs_nonneg _)
          _ = |deriv W x| := mul_one _
      · rw [Set.indicator_of_notMem hyI]
        simp
    unfold SpectrallyNegativeLevy.generatorIntegrand
    dsimp [B]
    exact (norm_sub_le _ _).trans (add_le_add hdiff hcomp)
  change IntegrableOn
    (SpectrallyNegativeLevy.generatorIntegrand W x) (Iio 0) X.ν
  exact
    integrableOn_Iio_zero_of_isBigO_sq_of_bound
      X.ν (levyWeight_integrable X)
      (SpectrallyNegativeLevy.generatorIntegrand W x) hF hsmall B hB hbound

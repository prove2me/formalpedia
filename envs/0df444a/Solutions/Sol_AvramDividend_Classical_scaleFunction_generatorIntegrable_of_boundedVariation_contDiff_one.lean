-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:58:20.747234+00:00
-- url     : https://prove2.me/submissions/f67b29c3-6589-41ea-ac23-9dd59f7198f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_bounds_of_nonpositive
import Theorems.Thm_AvramDividend_Classical_integrableOn_Iio_zero_of_isBigO_id_of_bound


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (x : ℝ) (hx : 0 < x)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0)) :
    X.GeneratorIntegrable W x := by
  have hνsq : Integrable (fun y : ℝ => min 1 (y ^ 2)) X.ν :=
    levyWeight_integrable X
  have hνabs : IntegrableOn (fun y : ℝ => |y|) (Ioo (-1 : ℝ) 0) X.ν := by
    change Integrable (fun y : ℝ => |y|) (X.ν.restrict (Ioo (-1 : ℝ) 0))
    have hm : AEStronglyMeasurable (fun y : ℝ => |y|)
        (X.ν.restrict (Ioo (-1 : ℝ) 0)) := by fun_prop
    have hn : 0 ≤ᵐ[X.ν.restrict (Ioo (-1 : ℝ) 0)] (fun y : ℝ => |y|) := by
      filter_upwards with y
      positivity
    exact (lintegral_ofReal_ne_top_iff_integrable hm hn).mp (ne_of_lt hbv.2)
  have hmono : Monotone W := by
    intro u v huv
    by_cases hv : v < 0
    · have hu : u < 0 := lt_of_le_of_lt huv hv
      rw [hW.1 u hu, hW.1 v hv]
    · have hv0 : 0 ≤ v := le_of_not_gt hv
      by_cases hu : u < 0
      · rw [hW.1 u hu]
        exact hW.2.1 v hv0
      · exact hW.2.2.2.1 (le_of_not_gt hu) hv0 huv
  have hWmeas : Measurable W := hmono.measurable
  have hF : AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand W x) X.ν := by
    have hshift : Measurable (fun y : ℝ => W (x + y)) :=
      hWmeas.comp (measurable_const.add measurable_id)
    have hind : Measurable (fun y : ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
      measurable_const.indicator measurableSet_Ioo
    have hgen : Measurable (SpectrallyNegativeLevy.generatorIntegrand W x) := by
      unfold SpectrallyNegativeLevy.generatorIntegrand
      exact (hshift.sub measurable_const).sub
        ((measurable_const.mul measurable_id).mul hind)
    exact hgen.aestronglyMeasurable
  have hcontAt : ContDiffAt ℝ 1 W x :=
    hC1.contDiffAt (isOpen_Ioi.mem_nhds hx)
  have hd : HasDerivAt W (deriv W x) x :=
    (hcontAt.differentiableAt (by norm_num)).hasDerivAt
  have hrem0 : (fun y : ℝ => W (x + y) - W x - y • deriv W x)
      =o[𝓝 0] (fun y : ℝ => y) :=
    hasDerivAt_iff_isLittleO_nhds_zero.mp hd
  have hrem : (fun y : ℝ => W (x + y) - W x - deriv W x * y)
      =o[𝓝 0] (fun y : ℝ => y) := by
    apply hrem0.congr_left
    intro y
    simp [smul_eq_mul, mul_comm]
  have hone : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    isOpen_Ioo.mem_nhds (by norm_num)
  have heq : (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand W x y)
      =ᶠ[𝓝 0] (fun y : ℝ => W (x + y) - W x - deriv W x * y) := by
    filter_upwards [hone] with y hy
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp [Set.indicator_of_mem hy]
  have hsmall : (fun y : ℝ => SpectrallyNegativeLevy.generatorIntegrand W x y)
      =O[𝓝 0] (fun y : ℝ => y) :=
    hrem.isBigO.congr' heq.symm Filter.EventuallyEq.rfl
  let B : ℝ := W x + |deriv W x|
  have hWx0 : 0 ≤ W x := hW.2.1 x hx.le
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbound : ∀ y : ℝ, y < 0 →
      ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤ B := by
    intro y hy
    have hs := scaleFunction_shift_bounds_of_nonpositive
      X q W hW x y hx.le (le_of_lt hy)
    have hdiff : |W (x + y) - W x| ≤ W x := by
      rw [abs_of_nonpos (sub_nonpos.mpr hs.2)]
      linarith [hs.1]
    have hind : |y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y| ≤ 1 := by
      by_cases hyI : y ∈ Ioo (-1 : ℝ) 1
      · have habs : |y| < 1 := abs_lt.mpr hyI
        simpa [Set.indicator, hyI] using habs.le
      · simp [Set.indicator, hyI]
    have hcomp : |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator
        (fun _ : ℝ => (1 : ℝ)) y| ≤ |deriv W x| := by
      rw [mul_assoc, abs_mul]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hind (abs_nonneg (deriv W x))
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [Real.norm_eq_abs]
    calc
      |W (x + y) - W x - deriv W x * y *
          (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y|
          ≤ |W (x + y) - W x| +
              |deriv W x * y * (Ioo (-1 : ℝ) 1).indicator
                (fun _ : ℝ => (1 : ℝ)) y| := abs_sub _ _
      _ ≤ W x + |deriv W x| := add_le_add hdiff hcomp
      _ = B := rfl
  exact integrableOn_Iio_zero_of_isBigO_id_of_bound X.ν hνsq hνabs
    (SpectrallyNegativeLevy.generatorIntegrand W x) hF hsmall B hB0 hbound

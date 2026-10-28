-- Prove2me | solution 1 for AvramDividend.Classical.real_nonnegative_density_measure_convolution_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:23:18.082512+00:00
-- url     : https://prove2.me/submissions/1f264a3b-996a-4918-89ce-f603ea8b48d5

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_convolution_lconvolution_ofReal_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Convolving measures with nonnegative real densities yields the measure
with the ordinary finite real convolution density. -/
theorem solution (κ f : ℝ → ℝ)
    (hκpos : ∀ y : ℝ, 0 ≤ κ y) (hfpos : ∀ y : ℝ, 0 ≤ f y)
    (hκmeas : Measurable κ) (hfmeas : Measurable f)
    (hconv : ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * f (x - y)) volume) :
    (volume.withDensity (fun y : ℝ => ENNReal.ofReal (κ y))).conv
      (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))) =
    volume.withDensity (fun x : ℝ =>
      ENNReal.ofReal (∫ y : ℝ, κ y * f (x - y) ∂volume)) := by
  have hκM : Measurable (fun y : ℝ => ENNReal.ofReal (κ y)) := by
    fun_prop
  have hfM : Measurable (fun y : ℝ => ENNReal.ofReal (f y)) := by
    fun_prop
  calc
    (volume.withDensity (fun y : ℝ => ENNReal.ofReal (κ y))).conv
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y))) =
      volume.withDensity
        (lconvolution (fun y : ℝ => ENNReal.ofReal (κ y))
          (fun y : ℝ => ENNReal.ofReal (f y)) volume) :=
      conv_withDensity_eq_lconvolution hκM hfM
    _ = volume.withDensity (fun x : ℝ =>
          ENNReal.ofReal (∫ y : ℝ, κ y * f (x - y) ∂volume)) := by
      congr 1
      funext x
      exact nonnegative_real_convolution_lconvolution_ofReal_bridge
        κ f x hκpos hfpos (hconv x)

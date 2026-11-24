-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.layercake
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:17:52.549824+00:00
-- url     : https://prove2.me/submissions/8d931b08-698a-48f1-987f-60288f792753

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution {f : ℝ → ENNReal} (hf_measurable : Measurable f) :
    ∫⁻ (x : ℝ), f x = ∫⁻ (t : ℝ) in Ioi 0, volume {x : ℝ | ENNReal.ofReal t ≤ f x} := by
  let ind (x t : ℝ) : ENNReal := if ENNReal.ofReal t ≤ f x then 1 else 0
  calc
    ∫⁻ (x : ℝ), f x = ∫⁻ (x : ℝ), ∫⁻ (t : ℝ) in Ioi 0, ind x t := by
      congr; ext x; symm
      calc
        ∫⁻ (t : ℝ) in Ioi 0, ind x t
            = ∫⁻ (t : ℝ) in Ioi 0, {t : ℝ | ENNReal.ofReal t ≤ f x}.indicator 1 t := by
          simp [ind, indicator]
        _ = ∫⁻ (t : ℝ) in {t : ℝ | ENNReal.ofReal t ≤ f x} ∩ (Ioi 0), 1 := by
          apply setLIntegral_indicator
          exact measurableSet_le ENNReal.measurable_ofReal measurable_const
        _ = volume {t : ℝ | ENNReal.ofReal t ≤ f x ∧ 0 < t} := by apply setLIntegral_one
        _ = f x := by
          by_cases hinf : f x = ⊤
          · simp only [hinf, le_top, true_and]; exact Real.volume_Ioi
          calc
            volume {t | ENNReal.ofReal t ≤ f x ∧ 0 < t}
                = volume {t | t ≤ (f x).toReal ∧ 0 < t} := by
              congr; ext t; simp only [and_congr_left_iff]; intro
              exact ENNReal.ofReal_le_iff_le_toReal hinf
            _ = volume (Ioc 0 (f x).toReal) := by congr; aesop
            _ = ENNReal.ofReal (f x).toReal := by simp
            _ = f x := ENNReal.ofReal_toReal_eq_iff.mpr hinf
    _ = ∫⁻ (t : ℝ) in Ioi 0, ∫⁻ (x : ℝ), ind x t := by
      apply lintegral_lintegral_swap
      exact Measurable.aemeasurable <|
        Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) (by fun_prop) (by fun_prop)
    _ = ∫⁻ (t : ℝ) in Ioi 0, volume {x : ℝ | ENNReal.ofReal t ≤ f x} := by
      congr; ext t
      calc
        ∫⁻ (x : ℝ), ind x t = ∫⁻ (x : ℝ), {x : ℝ | ENNReal.ofReal t ≤ f x}.indicator 1 x := by
          simp [ind, indicator]
        _ = ∫⁻ (x : ℝ) in {x : ℝ | ENNReal.ofReal t ≤ f x}, 1 := by
          apply lintegral_indicator
          exact measurableSet_le measurable_const hf_measurable
        _ = volume {x | ENNReal.ofReal t ≤ f x} := by apply setLIntegral_one
end GaussianPerimeter.VolumeComparison

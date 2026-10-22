-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_weighted_value_interval_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:37:04.309833+00:00
-- url     : https://prove2.me/submissions/ea41ee71-8551-4d1a-bd62-11d00cbda698

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! A monotone nonnegative scale value bounds its next weighted interval
integral from below by the interval length times the right-endpoint weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ a b : ℝ) (hθ : 0 ≤ θ) (hab : a ≤ b)
    (hWa : 0 ≤ W a) :
    IntervalIntegrable
      (fun x : ℝ => Real.exp (-(θ * x)) * W x) volume a b ∧
      (b - a) * (Real.exp (-(θ * b)) * W a) ≤
        (∫ x in a..b, Real.exp (-(θ * x)) * W x) := by
  have hmono := scaleFunction_monotone X q W hW
  have hWint : IntervalIntegrable W volume a b :=
    (hmono.monotoneOn _).intervalIntegrable
  have hcont : Continuous (fun x : ℝ => Real.exp (-(θ * x))) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hweighted : IntervalIntegrable
      (fun x : ℝ => Real.exp (-(θ * x)) * W x) volume a b :=
    hWint.continuousOn_mul hcont.continuousOn
  have hconst : IntervalIntegrable
      (fun _ : ℝ => Real.exp (-(θ * b)) * W a) volume a b :=
    intervalIntegrable_const
  have hpoint : ∀ x ∈ Ioo a b,
      Real.exp (-(θ * b)) * W a ≤ Real.exp (-(θ * x)) * W x := by
    intro x hx
    have hE : Real.exp (-(θ * b)) ≤ Real.exp (-(θ * x)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left hx.2.le hθ)
    calc
      Real.exp (-(θ * b)) * W a ≤ Real.exp (-(θ * x)) * W a :=
        mul_le_mul_of_nonneg_right hE hWa
      _ ≤ Real.exp (-(θ * x)) * W x :=
        mul_le_mul_of_nonneg_left (hmono hx.1.le) (Real.exp_pos _).le
  have hlower := intervalIntegral.integral_mono_on_of_le_Ioo
    hab hconst hweighted hpoint
  refine ⟨hweighted, ?_⟩
  convert hlower using 1 <;> simp [intervalIntegral.integral_const] <;> ring

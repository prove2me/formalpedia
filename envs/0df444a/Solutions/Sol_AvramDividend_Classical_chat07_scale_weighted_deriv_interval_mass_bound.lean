-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_weighted_deriv_interval_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:22:37.650856+00:00
-- url     : https://prove2.me/submissions/811118d6-95c0-47dd-b340-be742a646c70

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_deriv_nonneg
import Theorems.Thm_AvramDividend_Classical_chat07_scale_deriv_interval_integrable_and_mass_bound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The positive, decreasing exponential weight is dominated on each interval
by its value at the left endpoint; monotonicity controls derivative mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ a b : ℝ) (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
        (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x) volume a b ∧
      (∫ x in a..b, Real.exp (-(θ * x)) * deriv W x) ≤
        Real.exp (-(θ * a)) * (W b - W a) := by
  have hderiv :=
    (chat07_scale_deriv_interval_integrable_and_mass_bound X q W hW a b).1
  have hcont : Continuous (fun x : ℝ => Real.exp (-(θ * x))) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hweighted : IntervalIntegrable
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x) volume a b :=
    hderiv.continuousOn_mul hcont.continuousOn
  have hconst : IntervalIntegrable
      (fun x : ℝ => Real.exp (-(θ * a)) * deriv W x) volume a b :=
    hderiv.const_mul _
  have hpoint : ∀ x ∈ Ioo a b,
      Real.exp (-(θ * x)) * deriv W x ≤
        Real.exp (-(θ * a)) * deriv W x := by
    intro x hx
    have hE : Real.exp (-(θ * x)) ≤ Real.exp (-(θ * a)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left hx.1.le hθ)
    exact mul_le_mul_of_nonneg_right hE
      (scaleFunction_deriv_nonneg X q W hW x (lt_of_le_of_lt ha hx.1))
  have hfirst := intervalIntegral.integral_mono_on_of_le_Ioo
    hab hweighted hconst hpoint
  have hdelta : 0 ≤ W b - W a :=
    sub_nonneg.mpr ((scaleFunction_monotone X q W hW) hab)
  have hmass :=
    (chat07_scale_deriv_interval_integrable_and_mass_bound X q W hW a b).2
  have hmass_le : (∫ x in a..b, deriv W x) ≤ W b - W a := by
    rw [Set.uIcc_of_le hdelta] at hmass
    exact hmass.2
  refine ⟨hweighted, ?_⟩
  calc
    (∫ x in a..b, Real.exp (-(θ * x)) * deriv W x)
        ≤ (∫ x in a..b, Real.exp (-(θ * a)) * deriv W x) := hfirst
    _ = Real.exp (-(θ * a)) * (∫ x in a..b, deriv W x) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ Real.exp (-(θ * a)) * (W b - W a) :=
      mul_le_mul_of_nonneg_left hmass_le (Real.exp_pos _).le

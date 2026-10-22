-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_unweighted_kernel_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:15:51.434831+00:00
-- url     : https://prove2.me/submissions/c0a079c0-f4ab-4577-b9e0-f6335b7f22c0

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_ae_finite
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_time_weight_factor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical
/-- Almost-everywhere finiteness of the underlying, unweighted Esscher double-tail kernel. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ)
    (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    ∀ᵐ t : ℝ ∂volume,
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ) < ⊤ := by
  have hweighted :=
    gaussian_double_tail_kernel_ae_finite μ φ 1 hφ zero_lt_one hlevy
  filter_upwards [hweighted] with t ht
  let K : ℝ → ENNReal := fun z =>
    if 0 < t ∧ t < z then
      ENNReal.ofReal (z - t) *
        ENNReal.ofReal (Real.exp (-φ * z))
    else 0
  have hs : MeasurableSet {z : ℝ | 0 < t ∧ t < z} := by
    have h1 : MeasurableSet {z : ℝ | (0 : ℝ) < t} := by
      exact measurableSet_lt
        (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ)))
        (measurable_const : Measurable (fun _ : ℝ => t))
    have h2 : MeasurableSet {z : ℝ | t < z} := by
      exact measurableSet_lt
        (measurable_const : Measurable (fun _ : ℝ => t))
        measurable_id
    exact h1.inter h2
  have hk : Measurable (fun z : ℝ =>
      ENNReal.ofReal (z - t) *
        ENNReal.ofReal (Real.exp (-φ * z))) := by
    fun_prop
  have hmeas : Measurable K := by
    exact hk.ite hs measurable_const
  have hfactor (z : ℝ) :
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-(1 : ℝ) * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) =
      ENNReal.ofReal (Real.exp (-(1 : ℝ) * t)) * K z :=
    gaussian_double_tail_time_weight_factor φ 1 t z
  have hlin :
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-(1 : ℝ) * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ) =
      ENNReal.ofReal (Real.exp (-(1 : ℝ) * t)) *
        (∫⁻ z : ℝ, K z ∂μ) := by
    calc
      _ = (∫⁻ z : ℝ,
        ENNReal.ofReal (Real.exp (-(1 : ℝ) * t)) * K z ∂μ) := by
          apply lintegral_congr
          intro z
          exact hfactor z
      _ = _ := lintegral_const_mul _ hmeas
  rw [hlin] at ht
  have hcoef : 0 < ENNReal.ofReal (Real.exp (-(1 : ℝ) * t)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hfin : (∫⁻ z : ℝ, K z ∂μ) < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.mp ht with ⟨_, hi⟩ | hzero | hzero
    · exact hi
    · exact False.elim ((ne_of_gt hcoef) hzero)
    · simp [hzero]
  exact hfin

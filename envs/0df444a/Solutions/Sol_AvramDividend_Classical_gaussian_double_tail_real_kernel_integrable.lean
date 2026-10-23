-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_real_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:27:29.021966+00:00
-- url     : https://prove2.me/submissions/426af835-a34f-471f-9a7b-6c9b0049b7a6

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_global_kernel_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    Integrable (fun t : ℝ => (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ).toReal) volume := by
  have hpos : MeasurableSet
      {p : ℝ × ℝ | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hlt : MeasurableSet
      {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have hset : MeasurableSet
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := hpos.inter hlt
  have hprod : Measurable
      (fun p : ℝ × ℝ =>
        ENNReal.ofReal (p.2 - p.1) *
          ENNReal.ofReal (Real.exp (-(φ * p.2)))) := by
    fun_prop
  have hmeas_pair : Measurable
      (fun p : ℝ × ℝ =>
        if 0 < p.1 ∧ p.1 < p.2 then
          ENNReal.ofReal (p.2 - p.1) *
            ENNReal.ofReal (Real.exp (-(φ * p.2))) else 0) :=
    Measurable.ite hset hprod measurable_const
  have hmeas : Measurable
      (fun t : ℝ => ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ) :=
    Measurable.lintegral_prod_right hmeas_pair
  have hfin :=
    gaussian_double_tail_global_kernel_integrable μ φ hφ hlevy
  exact integrable_toReal_of_lintegral_ne_top
    hmeas.aemeasurable (ne_of_lt hfin)

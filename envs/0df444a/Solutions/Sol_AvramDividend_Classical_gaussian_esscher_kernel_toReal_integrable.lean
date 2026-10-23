-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_kernel_toReal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:23:30.362815+00:00
-- url     : https://prove2.me/submissions/707d1ce3-38ca-4905-b0d2-0375c5819797

import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_double_tail_global_mass_finite

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Finite nonnegative kernel mass gives real L1 integrability via toReal. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ]
    (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    Integrable (fun t : ℝ =>
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-(φ * z)))
         else 0) ∂μ).toReal) volume := by
  let F : ℝ → ℝ → ℝ≥0∞ := fun t z =>
    if 0 < t ∧ t < z then
      ENNReal.ofReal (z - t) *
        ENNReal.ofReal (Real.exp (-(φ * z)))
    else 0
  have hcond : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hFmeas : Measurable (Function.uncurry F) := by
    change Measurable (fun p : ℝ × ℝ =>
      if 0 < p.1 ∧ p.1 < p.2 then
        ENNReal.ofReal (p.2 - p.1) *
          ENNReal.ofReal (Real.exp (-(φ * p.2)))
      else 0)
    exact Measurable.ite hcond (by fun_prop) measurable_const
  have hFintegral : AEMeasurable
      (fun t : ℝ => ∫⁻ z : ℝ, F t z ∂μ) volume :=
    (Measurable.lintegral_prod_right (ν := μ) hFmeas).aemeasurable
  have hmass : (∫⁻ t : ℝ, ∫⁻ z : ℝ, F t z ∂μ ∂volume) < ⊤ := by
    simpa only [F] using
      gaussian_esscher_double_tail_global_mass_finite μ φ hφ hlevy
  have hfinal :=
    integrable_toReal_of_lintegral_ne_top hFintegral (ne_of_lt hmass)
  simpa only [F] using hfinal

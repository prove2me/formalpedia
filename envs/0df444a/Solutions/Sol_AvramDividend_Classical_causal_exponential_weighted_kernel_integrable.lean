-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponential_weighted_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:21:32.967356+00:00
-- url     : https://prove2.me/submissions/b93a2b81-c7d9-43de-98ef-8d3cff1463c2

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (K : ℝ → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-w * t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-w * t))
      (volume.restrict (Ioi (0 : ℝ))) := hcont.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖Real.exp (-w * t)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hwtx : -w * t ≤ 0 := by
      have hwt : 0 ≤ w * t := mul_nonneg hw ht.le
      nlinarith
    have hh : Real.exp (-w * t) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr hwtx
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.exp_zero] using hh
  have hMul := hK.bdd_mul hmeas hbound
  change Integrable (fun t : ℝ => Real.exp (-w * t) * K t)
      (volume.restrict (Ioi (0 : ℝ)))
  simpa only [mul_comm] using hMul

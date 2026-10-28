-- Prove2me | solution 1 for AvramDividend.Classical.exp_tilt_real_mgf_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:50:59.496239+00:00
-- url     : https://prove2.me/submissions/5bb5448e-6156-4cbe-b9f9-16052fb4359f

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (a s : ℝ) :
    (∫ x, Real.exp (s * x) ∂(μ.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x))))) =
    ∫ x, Real.exp ((a + s) * x) ∂μ := by
  have hf : Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (a * x))) :=
    ((measurable_const.mul measurable_id).exp).ennreal_ofReal
  have htop : ∀ᵐ x ∂μ,
      ENNReal.ofReal (Real.exp (a * x)) < ⊤ :=
    ae_of_all μ (fun x => lt_top_iff_ne_top.mpr (ENNReal.ofReal_ne_top))
  rw [integral_withDensity_eq_integral_toReal_smul hf htop]
  apply integral_congr_ae
  filter_upwards with x
  change (ENNReal.ofReal (Real.exp (a * x))).toReal *
    Real.exp (s * x) = Real.exp ((a + s) * x)
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, ← Real.exp_add]
  congr 1
  ring
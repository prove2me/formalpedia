-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T23:05:08.009988+00:00
-- url     : https://prove2.me/submissions/891728cc-238d-4d7f-80c8-f85332e62fd7

import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-- Tonelli interchange for the tilted negative-jump Gaussian double-tail kernel. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ ∂volume) =
    (∫⁻ z : ℝ, ∫⁻ t : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂volume ∂μ) := by
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.1} :=
      measurableSet_lt measurable_const measurable_fst
    have h2 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
      measurableSet_lt measurable_fst measurable_snd
    exact h1.inter h2
  have hk : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((p.2 - p.1) * Real.exp (-θ * p.1)) *
        ENNReal.ofReal (Real.exp (-φ * p.2))) := by
    fun_prop
  have hf : Measurable (fun p : ℝ × ℝ =>
      if 0 < p.1 ∧ p.1 < p.2 then
        ENNReal.ofReal ((p.2 - p.1) * Real.exp (-θ * p.1)) *
          ENNReal.ofReal (Real.exp (-φ * p.2))
      else 0) :=
    hk.ite hs measurable_const
  exact lintegral_lintegral_swap hf.aemeasurable

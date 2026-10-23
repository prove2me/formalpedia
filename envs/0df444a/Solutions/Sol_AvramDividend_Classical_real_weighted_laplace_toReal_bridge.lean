-- Prove2me | solution 1 for AvramDividend.Classical.real_weighted_laplace_toReal_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T15:00:40.16629+00:00
-- url     : https://prove2.me/submissions/b97c2f39-106c-4b7d-8c7e-b916a1f54d5e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (θ : ℝ) (f : ℝ → ENNReal)
    (hf : Measurable f)
    (hfin : (∫⁻ t : ℝ,
      ENNReal.ofReal (Real.exp (-(θ * t))) * f t ∂μ) < ⊤) :
    (∫ t : ℝ, Real.exp (-(θ * t)) * (f t).toReal ∂μ) =
      (∫⁻ t : ℝ,
        ENNReal.ofReal (Real.exp (-(θ * t))) * f t ∂μ).toReal := by
  have hweight : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(θ * t)))) := by
    fun_prop
  have hmeas : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(θ * t))) * f t) :=
    hweight.mul hf
  have hae : ∀ᵐ t : ℝ ∂μ,
      ENNReal.ofReal (Real.exp (-(θ * t))) * f t < ⊤ :=
    ae_lt_top hmeas (ne_of_lt hfin)
  calc
    (∫ t : ℝ, Real.exp (-(θ * t)) * (f t).toReal ∂μ) =
        ∫ t : ℝ,
          (ENNReal.ofReal (Real.exp (-(θ * t))) * f t).toReal ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact (ENNReal.toReal_ofReal_mul
        (Real.exp (-(θ * t))) (f t) (Real.exp_nonneg _)).symm
    _ = (∫⁻ t : ℝ,
          ENNReal.ofReal (Real.exp (-(θ * t))) * f t ∂μ).toReal :=
      integral_toReal hmeas.aemeasurable hae

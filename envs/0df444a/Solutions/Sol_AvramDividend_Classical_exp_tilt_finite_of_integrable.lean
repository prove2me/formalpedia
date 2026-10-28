-- Prove2me | solution 1 for AvramDividend.Classical.exp_tilt_finite_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:09:52.235982+00:00
-- url     : https://prove2.me/submissions/e6ba3593-ffab-4698-9869-fcee3bcac132

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) (a : ℝ)
    (h : Integrable (fun x : ℝ => Real.exp (a * x)) μ) :
    IsFiniteMeasure (μ.withDensity (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (a * x)))) := by
  exact isFiniteMeasure_withDensity_ofReal h.hasFiniteIntegral
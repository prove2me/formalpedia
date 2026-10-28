-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exponential_withDensity_nonzero_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:58:17.959891+00:00
-- url     : https://prove2.me/submissions/ab7c07e1-41c6-42e3-a341-1bd44ddbe5e9

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Real
open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (μ : Measure ℝ≥0) (hμ : μ ≠ 0) (φ : ℝ)
    (hf : AEMeasurable
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) μ) :
    μ.withDensity (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) ≠ 0 := by
  intro h
  have h0 := withDensity_eq_zero hf h
  apply hμ
  rw [Filter.EventuallyEq, ae_iff] at h0
  have hset : {z : ℝ≥0 | ¬ ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) = (0 : ℝ≥0 → ℝ≥0∞) z} =
      univ := by
    ext z
    simp [Real.exp_pos]
  rw [hset, Measure.measure_univ_eq_zero] at h0
  exact h0

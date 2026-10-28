-- Prove2me | solution 1 for AvramDividend.Classical.positive_discounted_first_moment_of_nonzero_no_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:01:33.767265+00:00
-- url     : https://prove2.me/submissions/d36495eb-1cf7-4862-bef4-0cf5b126c717

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_positive_first_moment_of_nonzero_without_zero_atom
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (μ : Measure ℝ≥0) (hzero : μ ({0} : Set ℝ≥0) = 0) (hμ : μ ≠ 0)
    (φ : ℝ)
    (hf : AEMeasurable
      (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) μ) :
    0 < ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂
      (μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))) := by
  have hne : μ.withDensity (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) ≠ 0 := by
    intro h
    have h0 := withDensity_eq_zero hf h
    apply hμ
    rw [Filter.EventuallyEq, ae_iff] at h0
    have hset : {z : ℝ≥0 | ¬ ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) =
        (0 : ℝ≥0 → ℝ≥0∞) z} = univ := by
      ext z
      simp [Real.exp_pos]
    rw [hset, Measure.measure_univ_eq_zero] at h0
    exact h0
  exact AvramDividend.Classical.positive_first_moment_of_nonzero_without_zero_atom _
    (withDensity_absolutelyContinuous _ _ hzero) hne

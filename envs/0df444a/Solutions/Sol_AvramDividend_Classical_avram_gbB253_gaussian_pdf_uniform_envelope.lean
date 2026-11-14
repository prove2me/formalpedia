-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB253_gaussian_pdf_uniform_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T15:46:18.175296+00:00
-- url     : https://prove2.me/submissions/9821bb08-72c5-4456-b94a-2ad1d8804d5c

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.Distributions.Gaussian.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

theorem solution
    (mu : ℝ) (v : ℝ≥0) (hv : 0 < v) (y : ℝ) :
    ProbabilityTheory.gaussianPDFReal mu v y ≤
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  have hreal : 0 < (v : ℝ) := by exact_mod_cast hv
  have hpos : 0 ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by positivity
  have hquot : -(y - mu)^2 / (2 * (v : ℝ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg (y - mu))
    · positivity
  have hexp : Real.exp (-(y - mu)^2 / (2 * (v : ℝ))) ≤ 1 := by
    exact (Real.exp_le_one_iff).2 hquot
  simpa only [mul_one] using (mul_le_mul_of_nonneg_left hexp hpos)

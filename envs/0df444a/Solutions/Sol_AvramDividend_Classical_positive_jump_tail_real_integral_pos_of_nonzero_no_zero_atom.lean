-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_tail_real_integral_pos_of_nonzero_no_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:51:48.198331+00:00
-- url     : https://prove2.me/submissions/57d3a64a-ef86-4867-94b8-78caf29aebf3

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_positive_first_moment_of_nonzero_without_zero_atom
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integral_eq_firstMoment_toReal
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution (μ : Measure ℝ≥0)
    (hzero : μ ({0} : Set ℝ≥0) = 0) (hμ : μ ≠ 0)
    (hfinite : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    0 < ∫ t in Ioi (0 : ℝ),
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal ∂volume := by
  rw [AvramDividend.Classical.positive_jump_tail_real_integral_eq_firstMoment_toReal μ hfinite]
  exact ENNReal.toReal_pos
    (AvramDividend.Classical.positive_first_moment_of_nonzero_without_zero_atom μ hzero hμ).ne'
    hfinite.ne

-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_tail_real_antitone_of_finite_firstMoment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:46:09.950591+00:00
-- url     : https://prove2.me/submissions/14c0ad72-d6ba-4905-8231-f4d5291e0fa9

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Layercake
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_antitone
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_threshold_mass_le_first_moment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (μ : Measure ℝ≥0)
    (hfirst : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    AntitoneOn (fun t : ℝ =>
      (μ {z : ℝ≥0 | t < (z : ℝ)}).toReal) (Ioi (0 : ℝ)) := by
  intro a ha b _ hab
  have hfin : μ {z : ℝ≥0 | a < (z : ℝ)} ≠ ⊤ := by
    intro htop
    have h := AvramDividend.Classical.positive_jump_tail_threshold_mass_le_first_moment μ a ha
    rw [htop, ENNReal.mul_top (by simpa using ha)] at h
    exact absurd (lt_of_le_of_lt h hfirst) (lt_irrefl _)
  exact ENNReal.toReal_mono hfin (AvramDividend.Classical.positive_jump_tail_antitone μ hab)

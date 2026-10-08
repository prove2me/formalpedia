-- Prove2me | solution 1 for AvramDividend.Classical.cstar_shape_of_attained_positive_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:03:20.207443+00:00
-- url     : https://prove2.me/submissions/bbbfac9e-e764-42af-9c42-d37010370760

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_global_lower_le_right_liminf
import Theorems.Thm_AvramDividend_Classical_secant_of_derivative_lower_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Complete positive-barrier denominator and secant package. The proof uses
an attained global derivative minimum, and the right-liminf inequality
handles the competing barrier at zero. -/
theorem solution (W : ℝ → ℝ)
    (hattain : (cstar W).toReal ∈ cstarSet W)
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hcont : ContinuousOn W (Set.Icc 0 (cstar W).toReal))
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal)) :
    ∃ d : ℝ, 0 < d ∧
      scaleDeriv W (cstar W).toReal = (d : EReal) ∧
      (∀ a : ℝ, 0 ≤ a →
        scaleDeriv W a = ⊤ ∨
          (scaleDeriv W a).toReal = 0 ∨
          d ≤ (scaleDeriv W a).toReal) ∧
      (∀ b x : ℝ, 0 ≤ b → b ≤ x →
        x ≤ (cstar W).toReal →
        (x - b) * d ≤ W x - W b) := by
  have hc : 0 < (cstar W).toReal := hattain.1
  have hbound :
      ((deriv W (cstar W).toReal : ℝ) : EReal) ≤ derivZeroPlus W :=
    deriv_global_lower_le_right_liminf W
      (deriv W (cstar W).toReal) hattain.2
  have hboundary : scaleDeriv W 0 = ⊤ ∨
      (scaleDeriv W 0).toReal = 0 ∨
      deriv W (cstar W).toReal ≤ (scaleDeriv W 0).toReal := by
    by_cases htop : scaleDeriv W 0 = ⊤
    · exact Or.inl htop
    · right
      right
      have hle :
          ((deriv W (cstar W).toReal : ℝ) : EReal) ≤ scaleDeriv W 0 := by
        simpa [scaleDeriv] using hbound
      have hnotbot :
          ((deriv W (cstar W).toReal : ℝ) : EReal) ≠ ⊥ := by
        simp
      have hreal := EReal.toReal_le_toReal hle hnotbot htop
      simpa using hreal
  refine ⟨deriv W (cstar W).toReal, hpositive, ?_, ?_, ?_⟩
  · simp [scaleDeriv, ne_of_gt hc]
  · intro a ha
    by_cases haz : a = 0
    · subst a
      exact hboundary
    · right
      right
      have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
      simpa [scaleDeriv, haz] using hattain.2 a hapos
  · exact secant_of_derivative_lower_bound W (cstar W).toReal
      (deriv W (cstar W).toReal) hcont hdiff
      (fun t ht => hattain.2 t ht.1)

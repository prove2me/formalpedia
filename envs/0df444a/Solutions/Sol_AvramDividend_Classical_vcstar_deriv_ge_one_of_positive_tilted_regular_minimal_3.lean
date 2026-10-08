-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_deriv_ge_one_of_positive_tilted_regular_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T14:17:54.212741+00:00
-- url     : https://prove2.me/submissions/5a9b4a4a-24c7-4beb-b852-09d19b961815

-- Alternative independent candidate for CE 6897; proof body unchanged.
import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal

open Set
open AvramDividend.Classical

-- Conditional analytic reduction, NOT a solution of the canonical M4 target.
-- Both theorem imports are Proved in saved authoritative records.
-- This source has not been compiled or submitted.
theorem solution (W : ℝ → ℝ)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ x : ℝ, 0 < x → 0 < W x)
    (φ : ℝ) (hφ : 0 < φ)
    (htilt : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) :
    ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (vcstar W) x ∧
      1 ≤ deriv (vcstar W) x := by
  have hpos : ∀ x : ℝ, 0 < x → 0 < deriv W x := by
    intro x hx
    have hdiff : DifferentiableAt ℝ W x :=
      ((hreg x hx).differentiableWithinAt one_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hx)
    exact lt_of_lt_of_le (mul_pos hφ (hpositive x hx))
      (normalized_derivative_lower_bound φ x htilt hx hdiff)
  exact vcstar_deriv_ge_one_of_regular_minimal W hreg hpos hmin

-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_ge_one_of_positive_tilted_regular_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T14:12:10.578995+00:00
-- url     : https://prove2.me/submissions/507e2bc0-8fab-4bcb-922a-ae1409c2cd21

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
      ((hreg.differentiableOn_one) x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
    exact lt_of_lt_of_le (mul_pos hφ (hpositive x hx))
      (normalized_derivative_lower_bound φ x htilt hx hdiff)
  exact vcstar_deriv_ge_one_of_regular_minimal W hreg hpos hmin

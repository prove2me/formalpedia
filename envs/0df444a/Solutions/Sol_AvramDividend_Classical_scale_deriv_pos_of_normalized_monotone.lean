-- Prove2me | solution 1 for AvramDividend.Classical.scale_deriv_pos_of_normalized_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:43:24.328105+00:00
-- url     : https://prove2.me/submissions/09b40d2f-62a7-495f-a95c-6ed5caa6578c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (φ : ℝ)
    (hφ : 0 < φ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hmono : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  intro x hx
  have hbound : φ * W x ≤ deriv W x :=
    normalized_derivative_lower_bound φ x hmono hx (hdiff x hx)
  exact lt_of_lt_of_le (mul_pos hφ (hpos x hx)) hbound

-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_quadratic_remainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/340dff1d-afdd-48e5-b230-a92e7eaaedf2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperImaginaryExp_neg
import Theorems.Thm_CohnElkies_upperImaginaryExp_quadratic_remainder_norm_le_of_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (x : ℝ) :
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ) +
          ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      |x| ^ 3 / 6 := by
  by_cases hx : 0 ≤ x
  · simpa [abs_of_nonneg hx] using!
      upperImaginaryExp_quadratic_remainder_norm_le_of_nonneg hx
  · have hxnegative : x < 0 := lt_of_not_ge hx
    have hf :
        upperImaginaryExp x =
          starRingEnd ℂ (upperImaginaryExp (-x)) := by
      simpa using! upperImaginaryExp_neg (-x)
    have hconj :
        upperImaginaryExp x - 1 -
            Complex.I * (x : ℂ) +
              ((x ^ 2 / 2 : ℝ) : ℂ) =
          starRingEnd ℂ
            (upperImaginaryExp (-x) - 1 -
              Complex.I * ((-x : ℝ) : ℂ) +
                (((-x) ^ 2 / 2 : ℝ) : ℂ)) := by
      have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
        simpa using! Complex.conj_ofReal (2 : ℝ)
      rw [hf]
      simp [htwo]
      ring
    calc
      ‖upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) +
            ((x ^ 2 / 2 : ℝ) : ℂ)‖ =
        ‖upperImaginaryExp (-x) - 1 -
          Complex.I * ((-x : ℝ) : ℂ) +
            (((-x) ^ 2 / 2 : ℝ) : ℂ)‖ := by
          rw [hconj, Complex.norm_conj]
      _ ≤ (-x) ^ 3 / 6 :=
        upperImaginaryExp_quadratic_remainder_norm_le_of_nonneg
          (by linarith)
      _ = |x| ^ 3 / 6 := by
        rw [abs_of_neg hxnegative]
end CohnElkies

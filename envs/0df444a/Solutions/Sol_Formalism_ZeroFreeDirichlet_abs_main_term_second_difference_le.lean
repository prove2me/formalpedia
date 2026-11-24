-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.abs_main_term_second_difference_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:43:14.981907+00:00
-- url     : https://prove2.me/submissions/450976a4-de8e-42ed-8035-167edc542b0f

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.ZeroFreeDirichlet
private theorem le_one_add_mul_log_one_add {h : ℝ} (hh : 0 ≤ h) : h ≤ (1 + h) * Real.log (1 + h) := by
  have h1 : (0:ℝ) < 1 + h := by linarith
  have t := Real.log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [Real.log_inv] at t
  have e : (1 + h) * (1 + h)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
  nlinarith [mul_le_mul_of_nonneg_left t h1.le]
end Formalism.ZeroFreeDirichlet
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {y h γ : ℝ} (hy : 0 < y) (hh : 0 < h) :
    |y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y| ≤ y ^ 2 * h ^ 2 := by
  have h1 : (0:ℝ) < 1 + h := by linarith
  have hlog : Real.log (y * (1 + h)) = Real.log y + Real.log (1 + h) :=
    Real.log_mul hy.ne' h1.ne'
  have key : y * ((y * (1 + h)) * Real.log (y * (1 + h)) - (1 + γ) * (y * (1 + h)))
      - (y * (1 + h)) * (y * Real.log y - (1 + γ) * y) - y * h * y
      = y ^ 2 * ((1 + h) * Real.log (1 + h) - h) := by
    rw [hlog]; ring
  rw [key]
  have hL1 : Real.log (1 + h) ≤ h := by
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hL2 := le_one_add_mul_log_one_add hh.le
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg y) (by linarith))]
  have t : (1 + h) * Real.log (1 + h) - h ≤ h ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL1 h1.le]
  nlinarith [mul_le_mul_of_nonneg_left t (sq_nonneg y)]
end Formalism.ZeroFreeDirichlet

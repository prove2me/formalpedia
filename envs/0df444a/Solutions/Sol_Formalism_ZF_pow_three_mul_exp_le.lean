-- Prove2me | solution 1 for Formalism.ZF.pow_three_mul_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:09.189736+00:00
-- url     : https://prove2.me/submissions/a65c68de-d525-4995-ab54-5236f02006d7

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) :
    s ^ 3 * Real.exp (-(c * s / 4)) ≤ 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by
  have hs0 : 0 ≤ c * s / 8 := by positivity
  have hA : 0 < Real.exp (-(c / 8) * s) := Real.exp_pos _
  have hEA : Real.exp (c * s / 8) * Real.exp (-(c / 8) * s) = 1 := by
    rw [← Real.exp_add, show c * s / 8 + -(c / 8) * s = 0 by ring, Real.exp_zero]
  have hsq : Real.exp (-(c * s / 4)) = Real.exp (-(c / 8) * s) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfact : (c * s / 8) ^ 3 ≤ 6 * Real.exp (c * s / 8) := by
    have h := Real.pow_div_factorial_le_exp (c * s / 8) hs0 3
    norm_num [Nat.factorial] at h
    linarith
  have hkey : (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ≤ 6 := by
    nlinarith [mul_le_mul_of_nonneg_right hfact hA.le]
  have hs3 : s ^ 3 = (8 / c) ^ 3 * (c * s / 8) ^ 3 := by
    field_simp
  rw [hsq, hs3]
  have hk : 0 < (8 / c) ^ 3 := by positivity
  calc (8 / c) ^ 3 * (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ^ 2
      = (8 / c) ^ 3 * ((c * s / 8) ^ 3 * Real.exp (-(c / 8) * s)) * Real.exp (-(c / 8) * s) := by ring
    _ ≤ (8 / c) ^ 3 * 6 * Real.exp (-(c / 8) * s) := by gcongr
    _ = 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by ring
end Formalism.ZF

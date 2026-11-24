-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.mul_le_of_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:09.386799+00:00
-- url     : https://prove2.me/submissions/521f03df-6d91-4413-97af-2ed57bed1ebd

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {y c₀ K lq : ℝ} (hy : 2 ≤ y) (hc0 : 0 < c₀) (hc01 : c₀ ≤ 1)
    (hK : K * Real.log 2 ≤ Real.log y) (hK0 : 0 ≤ K) (hlq0 : 0 ≤ lq)
    (hlq : lq ≤ c₀ / 4 * Real.sqrt (Real.log y)) :
    K * lq ≤ 16 * y * Real.exp (-(c₀ / 4) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hL2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl2 := Real.log_two_gt_d9
  have hyL : y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
  set L := Real.log y with hLdef
  have hL0 : 0 < L := by linarith
  set s := Real.sqrt L with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = L := Real.sq_sqrt hL0.le
  have hs_half : 1 / 2 ≤ s := by nlinarith
  have hKL : K ≤ 2 * L := by nlinarith
  have hlq' : lq ≤ s / 4 := by
    have : c₀ / 4 * s ≤ 1 / 4 * s := mul_le_mul_of_nonneg_right (by linarith) hs0
    linarith
  have hKlq : K * lq ≤ (2 * L) * (s / 4) := mul_le_mul hKL hlq' hlq0 (by positivity)
  have hexp : Real.exp (s ^ 2 / 2) ≤ y * Real.exp (-(c₀ / 4) * s) := by
    rw [hyL, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc01 hs0, mul_nonneg hs0 (sub_nonneg.mpr hs_half)]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2 / 2)
  have hpoly : (2 * L) * (s / 4) ≤ 16 * (1 + s ^ 2 / 2 + (s ^ 2 / 2) ^ 2 / 2) := by
    rw [← hss]; nlinarith [sq_nonneg (s ^ 2 - s), sq_nonneg s]
  have e : 16 * y * Real.exp (-(c₀ / 4) * s) = 16 * (y * Real.exp (-(c₀ / 4) * s)) := by ring
  rw [e]
  linarith
end Formalism.ZeroFreeDirichlet

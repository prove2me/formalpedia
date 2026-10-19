-- Prove2me | solution 1 for CohnElkies.shellOscillation_eq_sinc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/ade73537-8b67-4e9b-88bd-08d9c3332309

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution (B T : ℝ) :
    shellOscillation B T =
      1 - Real.sinc (T / 2) * Real.cos ((B + 1 / 2) * T) := by
  unfold shellOscillation
  by_cases hT : T = 0
  · simp [hT]
  · have hhalf : T / 2 ≠ 0 := by exact div_ne_zero hT (by norm_num)
    have hderiv (a : ℝ) :
        HasDerivAt (fun y : ℝ => y - Real.sin (y * T) / T)
          (1 - Real.cos (a * T)) a := by
      convert! (hasDerivAt_id a).sub
        (((Real.hasDerivAt_sin (a * T)).comp a
          ((hasDerivAt_id a).mul_const T)).div_const T) using 1
      field_simp
    have hint : IntervalIntegrable
        (fun a : ℝ => 1 - Real.cos (a * T)) volume B (B + 1) := by
      have hc : Continuous (fun a : ℝ => 1 - Real.cos (a * T)) := by
        fun_prop
      exact hc.intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun a _ => hderiv a) hint, Real.sinc_of_ne_zero hhalf]
    have hsin :
        Real.sin ((B + 1) * T) - Real.sin (B * T) =
          2 * Real.sin (T / 2) * Real.cos ((B + 1 / 2) * T) := by
      rw [Real.sin_sub_sin]
      congr 2 <;> congr 1 <;> ring
    field_simp
    ring_nf at hsin ⊢
    linarith
end CohnElkies

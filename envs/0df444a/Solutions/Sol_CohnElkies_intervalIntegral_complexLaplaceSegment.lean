-- Prove2me | solution 1 for CohnElkies.intervalIntegral_complexLaplaceSegment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/6816eda1-efe5-44a8-832a-b0ccf7e6f538

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_complexFrullaniSegment_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (z w : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1,
      (w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))) =
      complexFrullaniKernel z w x := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hderiv (s : ℝ) :
      HasDerivAt
        (fun r : ℝ =>
          -Complex.exp
            (-complexFrullaniSegment z w r * (x : ℂ)) /
              (x : ℂ))
        ((w - z) *
          Complex.exp
            (-complexFrullaniSegment z w s * (x : ℂ))) s := by
    have hinner :=
      (complexFrullaniSegment_hasDerivAt z w s).neg.mul_const
        (x : ℂ)
    convert! hinner.cexp.neg.div_const (x : ℂ) using 1
    · simp only [Pi.neg_apply]
      field_simp [hxc]
  have hcontinuous :
      Continuous (fun s : ℝ =>
        (w - z) *
          Complex.exp
            (-complexFrullaniSegment z w s * (x : ℂ))) := by
    unfold complexFrullaniSegment
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s)
    (hcontinuous.intervalIntegrable 0 1)]
  unfold complexFrullaniSegment complexFrullaniKernel
  push_cast
  simp only [zero_mul, one_mul, add_zero]
  ring_nf
end CohnElkies

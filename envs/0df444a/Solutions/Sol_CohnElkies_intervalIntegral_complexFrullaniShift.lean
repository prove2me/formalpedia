-- Prove2me | solution 1 for CohnElkies.intervalIntegral_complexFrullaniShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/0949770f-6724-4a9b-a9a2-064cc1ee9a69

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_intervalIntegral_complexLaplaceSegment

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
    (z : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1,
      complexFrullaniKernel (z + (s : ℂ)) 1 x) =
      complexWallisPhaseKernel z x := by
  have hxc : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx
  have hfirst :
      (∫ s in (0 : ℝ)..1,
        Complex.exp (-(z + (s : ℂ)) * (x : ℂ))) =
        complexFrullaniKernel z (z + 1) x := by
    convert!
      intervalIntegral_complexLaplaceSegment z (z + 1) hx
      using 1
    apply intervalIntegral.integral_congr
    intro s _
    unfold complexFrullaniSegment
    push_cast
    ring_nf
  have hfirstContinuous :
      Continuous
        (fun s : ℝ =>
          Complex.exp (-(z + (s : ℂ)) * (x : ℂ))) := by
    fun_prop
  have hconstantContinuous :
      Continuous
        (fun _ : ℝ => Complex.exp (-(x : ℂ))) :=
    continuous_const
  have hexponential :
      Complex.exp (-(z + 1) * (x : ℂ)) =
        Complex.exp (-z * (x : ℂ)) *
          Complex.exp (-(x : ℂ)) := by
    rw [show -(z + 1) * (x : ℂ) =
      -z * (x : ℂ) + -(x : ℂ) by ring,
      Complex.exp_add]
  unfold complexFrullaniKernel
  simp only [neg_one_mul]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      (hfirstContinuous.intervalIntegrable 0 1)
      (hconstantContinuous.intervalIntegrable 0 1),
    hfirst, intervalIntegral.integral_const]
  unfold complexFrullaniKernel complexWallisPhaseKernel
  simp only [sub_zero, one_smul]
  rw [hexponential]
  field_simp [hxc]
end CohnElkies

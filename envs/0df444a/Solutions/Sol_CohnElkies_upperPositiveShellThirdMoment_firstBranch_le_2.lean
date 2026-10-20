-- Prove2me | solution 2 for CohnElkies.upperPositiveShellThirdMoment_firstBranch_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:54:55.893508+00:00
-- url     : https://prove2.me/submissions/bea0921e-06e3-4339-ad0c-85857c3cea3e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {ε u : ℝ}
    (hε : 0 < ε) (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2) :
    upperPositiveShellThirdMoment ε (u - 1) ≤
      upperPositiveShellThirdMoment ε (ε / 2) := by
  unfold upperPositiveShellThirdMoment
  have hL : 0 < shellLocation ε := by unfold shellLocation; positivity
  apply intervalIntegral.integral_mono_on (by linarith)
  · apply Continuous.intervalIntegrable
    have := positiveShellDensity_continuous ε
    fun_prop
  · apply Continuous.intervalIntegrable
    have := positiveShellDensity_continuous ε
    fun_prop
  · intro a ha
    have ha0 : 0 ≤ a := by linarith [ha.1]
    have hd : 0 ≤ positiveShellDensity ε a := by
      unfold positiveShellDensity shellWeight
      exact div_nonneg (Real.exp_pos _).le (Real.cosh_pos a).le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Real.cosh_abs ((1 + (u - 1)) * a), ← Real.cosh_abs ((1 + ε / 2) * a)]
    apply Real.cosh_le_cosh.mpr
    rw [abs_abs, abs_abs, abs_mul, abs_mul, abs_of_nonneg ha0]
    apply mul_le_mul_of_nonneg_right _ ha0
    rw [abs_le]
    constructor
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith


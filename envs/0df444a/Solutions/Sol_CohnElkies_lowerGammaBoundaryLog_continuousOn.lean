-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/6da342d6-6715-44b4-987e-7a7bab364ca4

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) {S : Set ℝ}
    (hS : ∀ y ∈ S, y ≠ 0) :
    ContinuousOn (lowerGammaBoundaryLog ℓ R) S := by
  have hnumPole (y : ℝ) (hy : y ∈ S) :
      ∀ m : ℕ,
        -Complex.I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have him := congrArg Complex.im hm
    norm_num at him
    exact hS y hy (by linarith)
  have hdenPole (y : ℝ) :
      ∀ m : ℕ,
        (ℓ : ℂ) + Complex.I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hnum :
      ContinuousOn
        (fun y : ℝ => Complex.Gamma (-Complex.I * (y : ℂ) / 2)) S := by
    intro y hy
    have harg :
        ContinuousAt (fun u : ℝ => -Complex.I * (u : ℂ) / 2) y := by
      fun_prop
    apply ContinuousAt.continuousWithinAt
    simpa [Function.comp_def] using!
      (Complex.continuousAt_Gamma
        (-Complex.I * (y : ℂ) / 2) (hnumPole y hy)).comp_of_eq
        harg (by rfl)
  have hden :
      ContinuousOn
        (fun y : ℝ =>
          Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)) S := by
    intro y hy
    have harg :
        ContinuousAt
          (fun u : ℝ => (ℓ : ℂ) + Complex.I * (u : ℂ) / 2) y := by
      fun_prop
    apply ContinuousAt.continuousWithinAt
    simpa [Function.comp_def] using!
      (Complex.continuousAt_Gamma
        ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2) (hdenPole y)).comp_of_eq
        harg (by rfl)
  have hnumlog :
      ContinuousOn
        (fun y : ℝ =>
          Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖) S := by
    apply hnum.norm.log
    intro y hy
    exact norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero (hnumPole y hy))
  have hdenlog :
      ContinuousOn
        (fun y : ℝ =>
          Real.log
            ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) S := by
    apply hden.norm.log
    intro y hy
    exact norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero (hdenPole y))
  change ContinuousOn
    (fun y : ℝ =>
      ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
        Real.log
          ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) S
  exact (continuousOn_const.add hnumlog).sub hdenlog
end CohnElkies

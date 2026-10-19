-- Prove2me | solution 1 for CohnElkies.saddle_complexShellInterval_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/cf7c9027-bf33-4bce-b1b7-f186df1919df

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddle_shifted_complexCos_re

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
    (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (T u : ℝ) :
    (∫ x in a..b,
      (w x : ℂ) *
        (Complex.cos
          ((x : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)).re =
      ∫ x in a..b,
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1) := by
  let F : ℝ → ℂ := fun x =>
    (w x : ℂ) *
      (Complex.cos
        ((x : ℂ) *
          ((T : ℂ) + Complex.I * (u : ℂ))) - 1)
  have hwcomplex : ContinuousOn
      (fun x : ℝ => (w x : ℂ))
      (Icc a b) :=
    Complex.ofRealCLM.continuous.comp_continuousOn hw
  have hkernel : Continuous
      (fun x : ℝ =>
        Complex.cos
          ((x : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1) := by
    fun_prop
  have hF : IntervalIntegrable F volume a b := by
    exact (hwcomplex.mul hkernel.continuousOn).intervalIntegrable_of_Icc
      hab
  calc
    (∫ x in a..b,
      (w x : ℂ) *
        (Complex.cos
          ((x : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)).re =
      ∫ x in a..b, (F x).re := by
        exact (Complex.reCLM.intervalIntegral_comp_comm hF).symm
    _ = ∫ x in a..b,
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1) := by
      apply intervalIntegral.integral_congr
      intro x hx
      try dsimp [F]
      rw [Complex.mul_re, Complex.sub_re,
        saddle_shifted_complexCos_re]
      simp
end CohnElkies

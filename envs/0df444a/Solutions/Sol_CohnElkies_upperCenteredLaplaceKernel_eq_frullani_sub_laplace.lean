-- Prove2me | solution 1 for CohnElkies.upperCenteredLaplaceKernel_eq_frullani_sub_laplace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/eddb0f68-bbf3-49ac-b38b-754b67d000c1

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    (c T : ℝ) {a : ℝ} (ha : a ≠ 0) :
    upperCenteredLaplaceKernel c T a =
      complexFrullaniKernel
        ((c : ℂ) - Complex.I * (T : ℂ))
        (c : ℂ) a -
      Complex.I * (T : ℂ) *
        Complex.exp (-(c : ℂ) * (a : ℂ)) := by
  have hbase :
      Complex.exp (-(c : ℂ) * (a : ℂ)) =
        (Real.exp (-c * a) : ℂ) := by
    calc
      Complex.exp (-(c : ℂ) * (a : ℂ)) =
          Complex.exp ((-c * a : ℝ) : ℂ) := by
        congr 1
        push_cast
        ring
      _ = (Real.exp (-c * a) : ℂ) := by
        exact (Complex.ofReal_exp (-c * a)).symm
  have hosc :
      Complex.exp
          (-((c : ℂ) - Complex.I * (T : ℂ)) *
            (a : ℂ)) =
        (Real.exp (-c * a) : ℂ) *
          upperImaginaryExp (a * T) := by
    have harg :
        -((c : ℂ) - Complex.I * (T : ℂ)) *
            (a : ℂ) =
          ((-c * a : ℝ) : ℂ) +
            Complex.I * ((a * T : ℝ) : ℂ) := by
      push_cast
      ring
    unfold upperImaginaryExp
    rw [harg, Complex.exp_add,
      ← Complex.ofReal_exp]
  unfold upperCenteredLaplaceKernel
    complexFrullaniKernel
  rw [hosc, hbase]
  push_cast
  have hac : (a : ℂ) ≠ 0 := by
    exact_mod_cast ha
  field_simp [hac]
end CohnElkies

-- Prove2me | solution 2 for CohnElkies.upperCenteredLaplaceKernel_eq_frullani_sub_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:36:06.697672+00:00
-- url     : https://prove2.me/submissions/14689399-18fb-4fe1-bddb-b2026a8f7480

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


theorem solution
    (c T : ℝ) {a : ℝ} (ha : a ≠ 0) :
    upperCenteredLaplaceKernel c T a =
      complexFrullaniKernel
        ((c : ℂ) - Complex.I * (T : ℂ))
        (c : ℂ) a -
      Complex.I * (T : ℂ) *
        Complex.exp (-(c : ℂ) * (a : ℂ)) := by
  unfold upperCenteredLaplaceKernel complexFrullaniKernel upperImaginaryExp
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hE : Complex.exp (-((c : ℂ) - Complex.I * (T : ℂ)) * (a : ℂ)) =
      Complex.exp (-(c : ℂ) * (a : ℂ)) * Complex.exp (Complex.I * ((a * T : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hE]
  push_cast
  field_simp <;> ring


-- Prove2me | solution 1 for CohnElkies.saddleSourceShiftedCosine_eq_imaginaryExponentials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/4020055f-15c3-4bcc-83e2-647504d7f1bf

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
namespace CohnElkies
theorem _root_.solution
    (a u T : ℝ) :
    Complex.cos
        ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) =
      ((Real.exp (-(u * a)) / 2 : ℝ) : ℂ) *
          upperImaginaryExp (a * T) +
        ((Real.exp (u * a) / 2 : ℝ) : ℂ) *
          upperImaginaryExp (-(a * T)) := by
  have hfirst :
      Complex.exp
          (((a : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) * Complex.I) =
        (Real.exp (-(u * a)) : ℂ) *
          upperImaginaryExp (a * T) := by
    unfold upperImaginaryExp
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  have hsecond :
      Complex.exp
          (-((a : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) * Complex.I) =
        (Real.exp (u * a) : ℂ) *
          upperImaginaryExp (-(a * T)) := by
    unfold upperImaginaryExp
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
    simp [Complex.I_sq]
  unfold Complex.cos
  rw [hfirst, hsecond]
  push_cast
  ring
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.radialGammaBoundaryExponent_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/5b2d4c29-bf55-4b0d-938a-5b371d4530a6

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    (d : ℕ) (R A B : ℝ)
    (hR : 0 < R) (hA : 0 < A) (hB : 0 < B) :
    Real.exp
        (((d : ℝ) / 2) * Real.log (Real.pi * R ^ 2) +
          Real.log A - Real.log B) =
      Real.exp ((d : ℝ) * Real.log R) *
        Real.pi ^ ((d : ℝ) / 2) * (A / B) := by
  have hlog :
      Real.log (Real.pi * R ^ 2) =
        Real.log Real.pi + 2 * Real.log R := by
    rw [Real.log_mul Real.pi_ne_zero
      (pow_ne_zero 2 hR.ne'), Real.log_pow]
    norm_num
  have hscale :
      Real.exp (((d : ℝ) / 2) *
        Real.log (Real.pi * R ^ 2)) =
      Real.exp ((d : ℝ) * Real.log R) *
        Real.pi ^ ((d : ℝ) / 2) := by
    rw [hlog, mul_add, Real.exp_add,
      Real.rpow_def_of_pos Real.pi_pos]
    have hdouble :
        ((d : ℝ) / 2) * (2 * Real.log R) =
          (d : ℝ) * Real.log R := by
      ring
    rw [hdouble]
    rw [show ((d : ℝ) / 2) * Real.log Real.pi =
      Real.log Real.pi * ((d : ℝ) / 2) by ring]
    ring
  rw [Real.exp_sub, Real.exp_add,
    Real.exp_log hA, Real.exp_log hB, hscale]
  ring
end CohnElkies

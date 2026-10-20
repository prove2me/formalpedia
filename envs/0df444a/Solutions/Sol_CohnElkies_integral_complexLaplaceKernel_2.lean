-- Prove2me | solution 2 for CohnElkies.integral_complexLaplaceKernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:35.590004+00:00
-- url     : https://prove2.me/submissions/f86ee40a-f15f-41f7-8c11-4118bb68732b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ))) = z⁻¹ := by
  rw [integral_exp_mul_complex_Ioi (a := -z) (by simp; linarith) 0]
  simp


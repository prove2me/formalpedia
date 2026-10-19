-- Prove2me | solution 2 for CohnElkies.complexLaplaceKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:49.339767+00:00
-- url     : https://prove2.me/submissions/68b9ad46-8a63-4251-8c30-1313175f397f

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
    IntegrableOn (fun x : ℝ => Complex.exp (-z * (x : ℂ))) (Ioi 0) := by
  exact integrableOn_exp_mul_complex_Ioi (a := -z) (by simp; linarith) 0


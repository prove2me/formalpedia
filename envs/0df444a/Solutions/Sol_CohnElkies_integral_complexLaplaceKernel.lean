-- Prove2me | solution 1 for CohnElkies.integral_complexLaplaceKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/be6c5c40-fb45-4e40-91e5-ce5c9126129b

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
namespace CohnElkies
theorem _root_.solution {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ))) = z⁻¹ := by
  have hneg : (-z).re < 0 := by
    simpa using! hz
  simpa [div_eq_mul_inv] using!
    (integral_exp_mul_complex_Ioi (a := -z) hneg 0)
end CohnElkies

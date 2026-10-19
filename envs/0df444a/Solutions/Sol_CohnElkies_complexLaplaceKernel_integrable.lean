-- Prove2me | solution 1 for CohnElkies.complexLaplaceKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/f620b20a-3cc5-4714-a9f7-2ce951704f0d

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
    IntegrableOn (fun x : ℝ => Complex.exp (-z * (x : ℂ))) (Ioi 0) := by
  have hneg : (-z).re < 0 := by
    simpa using! hz
  simpa only [neg_mul] using!
    (integrableOn_exp_mul_complex_Ioi (a := -z) hneg 0)
end CohnElkies

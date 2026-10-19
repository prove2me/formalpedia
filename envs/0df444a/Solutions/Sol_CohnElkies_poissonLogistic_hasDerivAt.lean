-- Prove2me | solution 1 for CohnElkies.poissonLogistic_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/c64dca45-1d1b-4fca-92c3-a44cd00af83a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    HasDerivAt poissonLogistic (poissonLogisticDensity u) u := by
  have he :=
    (Real.hasDerivAt_exp (Real.pi * u)).comp u
      ((hasDerivAt_id u).const_mul Real.pi)
  have hden : 1 + Real.exp (Real.pi * u) ≠ 0 := by
    positivity
  have hquot := he.div ((hasDerivAt_const u 1).add he) hden
  convert! hquot using 1
  unfold poissonLogisticDensity
  simp only [Function.comp_apply, Pi.add_apply, mul_one, zero_add]
  field_simp [hden]
  ring
end CohnElkies

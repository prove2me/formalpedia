-- Prove2me | solution 2 for CohnElkies.poissonLogistic_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:15.223746+00:00
-- url     : https://prove2.me/submissions/902a966d-e4c1-4f85-969a-84862abf9f14

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


theorem solution (u : ℝ) :
    HasDerivAt poissonLogistic (poissonLogisticDensity u) u := by
  have hf : HasDerivAt (fun u : ℝ => Real.exp (Real.pi * u)) (Real.exp (Real.pi * u) * Real.pi) u := by
    simpa using ((hasDerivAt_id u).const_mul Real.pi).exp
  have hg : HasDerivAt (fun u : ℝ => 1 + Real.exp (Real.pi * u)) (Real.exp (Real.pi * u) * Real.pi) u :=
    hf.const_add 1
  have hne : (1 + Real.exp (Real.pi * u)) ≠ 0 := by positivity
  have h := (hf.div hg hne).congr_deriv (g' := poissonLogisticDensity u) (by
    unfold poissonLogisticDensity
    ring)
  exact h


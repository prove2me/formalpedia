-- Prove2me | solution 2 for CohnElkies.poissonLogisticDensity_eq_limitingStripPoissonDensity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:02.992878+00:00
-- url     : https://prove2.me/submissions/d6028085-54d0-4d37-b338-7fa081d4bddc

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


theorem solution
    (u : ℝ) :
    poissonLogisticDensity u =
      2 * limitingStripPoissonDensity (2 * u) := by
  unfold poissonLogisticDensity limitingStripPoissonDensity
  have he := Real.exp_pos (Real.pi * u)
  have hc : Real.cosh (Real.pi * (2 * u) / 2) = (Real.exp (Real.pi * u) + (Real.exp (Real.pi * u))⁻¹) / 2 := by
    rw [Real.cosh_eq, show Real.pi * (2 * u) / 2 = Real.pi * u by ring, Real.exp_neg]
  rw [hc]
  field_simp
  ring


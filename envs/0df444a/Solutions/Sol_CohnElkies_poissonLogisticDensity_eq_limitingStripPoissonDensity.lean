-- Prove2me | solution 1 for CohnElkies.poissonLogisticDensity_eq_limitingStripPoissonDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/f0831659-c834-46b3-9022-acf4ca7b5cbb

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
theorem _root_.solution
    (u : ℝ) :
    poissonLogisticDensity u =
      2 * limitingStripPoissonDensity (2 * u) := by
  have he : Real.exp (Real.pi * u) ≠ 0 :=
    (Real.exp_pos _).ne'
  unfold poissonLogisticDensity limitingStripPoissonDensity
  have harg : Real.pi * (2 * u) / 2 = Real.pi * u := by
    ring
  rw [harg, Real.cosh_eq, Real.exp_neg]
  field_simp [he]; ring
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.lowerPoissonEndpointSharpCoefficient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/05d28644-095a-468a-8f76-e8bc29d83d36

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one

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
    {c : ℝ} (hc : 0 < c) :
    Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
        limitingPoissonEndpointExpectation =
      Real.log (Real.pi ^ 2 * c ^ 2) := by
  rw [limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one]
  have hleft : 2 * Real.pi * Real.exp 1 * c ^ 2 ≠ 0 := by
    positivity
  have hright : Real.pi / 2 ≠ 0 := by
    positivity
  have hfactor :
      (2 * Real.pi * Real.exp 1 * c ^ 2) *
          (Real.pi / 2) =
        (Real.pi ^ 2 * c ^ 2) * Real.exp 1 := by
    ring
  calc
    Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
        (Real.log (Real.pi / 2) - 1) =
      Real.log
        ((2 * Real.pi * Real.exp 1 * c ^ 2) *
          (Real.pi / 2)) - 1 := by
        rw [Real.log_mul hleft hright]
        ring
    _ = Real.log (Real.pi ^ 2 * c ^ 2) := by
      rw [hfactor,
        Real.log_mul
          (show Real.pi ^ 2 * c ^ 2 ≠ 0 by positivity)
          (show Real.exp (1 : ℝ) ≠ 0 by positivity),
        Real.log_exp]
      ring
end CohnElkies

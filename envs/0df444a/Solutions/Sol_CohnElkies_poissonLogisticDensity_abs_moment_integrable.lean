-- Prove2me | solution 1 for CohnElkies.poissonLogisticDensity_abs_moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/50f1fc54-1c40-480d-9a95-be5f34d7c2b0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integrable_abs_pow_mul_exp_neg_mul_abs
import Theorems.Thm_CohnElkies_poissonLogisticDensity_integrable
import Theorems.Thm_CohnElkies_poissonLogisticDensity_le_pi_exp

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (n : ℕ) :
    Integrable
      (fun u : ℝ => poissonLogisticDensity u * |u| ^ n) := by
  have hmajor :=
    (integrable_abs_pow_mul_exp_neg_mul_abs n Real.pi_pos).const_mul
      Real.pi
  apply hmajor.mono'
    (poissonLogisticDensity_integrable.aestronglyMeasurable.mul
      ((continuous_abs.pow n).aestronglyMeasurable))
  filter_upwards [] with u
  have hdensity : 0 < poissonLogisticDensity u := by
    unfold poissonLogisticDensity
    positivity
  have hmoment : 0 ≤ |u| ^ n := pow_nonneg (abs_nonneg _) _
  change
    |poissonLogisticDensity u * |u| ^ n| ≤
      Real.pi * (|u| ^ n * Real.exp (-Real.pi * |u|))
  rw [abs_of_nonneg (mul_nonneg hdensity.le hmoment)]
  calc
    poissonLogisticDensity u * |u| ^ n ≤
      (Real.pi * Real.exp (-Real.pi * |u|)) * |u| ^ n :=
      mul_le_mul_of_nonneg_right
        (poissonLogisticDensity_le_pi_exp u) hmoment
    _ = Real.pi * (|u| ^ n * Real.exp (-Real.pi * |u|)) := by
      ring
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.poissonLogistic_cosine_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/4fe1de6a-abd1-4525-a89e-fa2ec8e719ce

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogisticDensity_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (t : ℝ) :
    Integrable
      (fun u : ℝ =>
        poissonLogisticDensity u * Real.cos (t * u)) := by
  have hcontinuous :
      Continuous (fun u : ℝ => Real.cos (t * u)) := by
    fun_prop
  apply poissonLogisticDensity_integrable.mono'
    (poissonLogisticDensity_integrable.aestronglyMeasurable.mul
      hcontinuous.aestronglyMeasurable)
  filter_upwards [] with u
  have hpositive : 0 < poissonLogisticDensity u := by
    unfold poissonLogisticDensity
    positivity
  change
    |poissonLogisticDensity u * Real.cos (t * u)| ≤
      poissonLogisticDensity u
  rw [abs_mul, abs_of_pos hpositive]
  exact mul_le_of_le_one_right hpositive.le
    (Real.abs_cos_le_one _)
end CohnElkies

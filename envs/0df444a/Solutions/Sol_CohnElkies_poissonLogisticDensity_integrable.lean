-- Prove2me | solution 1 for CohnElkies.poissonLogisticDensity_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/b1a7792f-545d-4fef-90ce-40769c467419

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_limitingStripPoissonDensity_integrable
import Theorems.Thm_CohnElkies_poissonLogisticDensity_eq_limitingStripPoissonDensity

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    Integrable poissonLogisticDensity := by
  have hscaled :=
    limitingStripPoissonDensity_integrable.comp_mul_left'
      (by norm_num : (2 : ℝ) ≠ 0)
  apply (hscaled.const_mul (2 : ℝ)).congr
  filter_upwards [] with u
  exact (poissonLogisticDensity_eq_limitingStripPoissonDensity u).symm
end CohnElkies

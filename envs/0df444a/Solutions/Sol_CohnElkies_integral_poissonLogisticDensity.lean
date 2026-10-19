-- Prove2me | solution 1 for CohnElkies.integral_poissonLogisticDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/12cedfd4-13d6-4666-95da-604afa394660

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integral_poissonLogistic_change_Ioo

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
    (∫ u : ℝ, poissonLogisticDensity u) = 1 := by
  have h := integral_poissonLogistic_change_Ioo
    (fun _ : ℝ => (1 : ℝ))
  simpa [smul_eq_mul] using! h.symm
end CohnElkies

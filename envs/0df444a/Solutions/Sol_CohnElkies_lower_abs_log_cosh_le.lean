-- Prove2me | solution 1 for CohnElkies.lower_abs_log_cosh_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/182b2801-0c6e-44a8-8128-f2358df8c45e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_cosh_le_exp

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (Real.cosh x)| ≤ x := by
  rw [abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh x))]
  have hlog := Real.log_le_log
    (Real.cosh_pos x) (lower_cosh_le_exp hx)
  simpa using! hlog
end CohnElkies

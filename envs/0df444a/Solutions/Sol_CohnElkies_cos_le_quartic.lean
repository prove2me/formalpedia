-- Prove2me | solution 1 for CohnElkies.cos_le_quartic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/1f90d636-c027-45ab-9214-4a06486dc421

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96 : ℝ) := by
  have hbound := Real.cos_bound (show |x| ≤ 1 by simpa [abs_of_nonneg hx0] using! hx1)
  rw [abs_of_nonneg hx0] at hbound
  linarith [(le_abs_self (Real.cos x - (1 - x ^ 2 / 2)))]
end CohnElkies

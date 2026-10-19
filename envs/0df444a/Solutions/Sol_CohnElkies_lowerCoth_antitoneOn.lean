-- Prove2me | solution 1 for CohnElkies.lowerCoth_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/70713c04-2623-4cee-951d-45187d94df96

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution :
    AntitoneOn lowerCoth (Ioi (0 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact (lowerCoth_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa using! hx
    exact (lowerCoth_hasDerivAt hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa using! hx
    rw [(lowerCoth_hasDerivAt hx').deriv]
    exact neg_nonpos.mpr (sq_nonneg _)
end CohnElkies

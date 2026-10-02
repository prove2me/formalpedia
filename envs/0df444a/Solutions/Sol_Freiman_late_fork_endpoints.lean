-- Prove2me | solution 1 for Freiman.late_fork_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-16T10:56:05.506373+00:00
-- url     : https://prove2.me/submissions/e972b655-3324-449a-b70b-50f620ea1f62

import Theorems.Thm_Freiman_late_fork_endpoints_unswapped
import Theorems.Thm_Freiman_late_fork_endpoints_swapped
open Freiman
set_option autoImplicit false

-- Split incoming-order fork alignment on the recorded width orientation.
theorem solution (p : LowerPair) (path : LatePath)
    (hm : lateMatches p path.right3)
    (hv : latePathValid lateCatalog path)
    (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n) :
    lateForkAlignment p path := by
  intro n hmem d hd upper
  cases hw : n.wide
  · exact late_fork_endpoints_unswapped p path hm hv hn n hmem d hd upper hw
  · exact late_fork_endpoints_swapped p path hm hv hn n hmem d hd upper hw

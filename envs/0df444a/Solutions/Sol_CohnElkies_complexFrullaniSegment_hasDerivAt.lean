-- Prove2me | solution 1 for CohnElkies.complexFrullaniSegment_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/71c20252-4405-4e6a-9ece-74f941b69bc4

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (z w : ℂ) (s : ℝ) :
    HasDerivAt (complexFrullaniSegment z w) (w - z) s := by
  have hcomplex :
      HasDerivAt (fun q : ℂ => z + q * (w - z))
        (w - z) (s : ℂ) := by
    convert! (hasDerivAt_const (s : ℂ) z).add
      ((hasDerivAt_id (s : ℂ)).mul_const (w - z)) using 1
    all_goals simp
  change HasDerivAt
    (fun r : ℝ => z + (r : ℂ) * (w - z)) (w - z) s
  exact hcomplex.comp_ofReal
end CohnElkies

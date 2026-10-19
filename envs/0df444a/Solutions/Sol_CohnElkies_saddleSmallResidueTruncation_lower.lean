-- Prove2me | solution 1 for CohnElkies.saddleSmallResidueTruncation_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/133171d5-dce7-43e8-991e-b32c2112aa9a

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
    (ℓ : ℝ) :
    20 * Real.log ℓ ≤
      (saddleSmallResidueTruncation ℓ : ℝ) := by
  exact Nat.le_ceil (20 * Real.log ℓ)
end CohnElkies

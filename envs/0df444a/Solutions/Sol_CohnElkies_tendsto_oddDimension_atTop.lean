-- Prove2me | solution 1 for CohnElkies.tendsto_oddDimension_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/597579ed-5bc3-49b9-9b3a-abb7f88489da

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
  exact tendsto_atTop_mono
    (fun k => by change k ≤ 2 * k + 1; omega) tendsto_id
end CohnElkies

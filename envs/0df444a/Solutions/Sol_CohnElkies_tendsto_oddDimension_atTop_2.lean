-- Prove2me | solution 2 for CohnElkies.tendsto_oddDimension_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:17.160988+00:00
-- url     : https://prove2.me/submissions/d74a3e92-4cb4-4e22-bc30-22d0754d89a2

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


theorem solution :
    Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop := by
  exact Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩


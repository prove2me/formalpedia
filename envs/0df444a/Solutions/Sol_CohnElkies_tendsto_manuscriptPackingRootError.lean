-- Prove2me | solution 1 for CohnElkies.tendsto_manuscriptPackingRootError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/a18770f0-fef0-4010-a4d5-4d38fdb4f55a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (hpacking : SharpPackingRootAsymptotic) :
    Tendsto manuscriptPackingRootError atTop (nhds (0 : ℝ)) := by
  unfold SharpPackingRootAsymptotic at hpacking
  have hconstant :
      Tendsto (fun _ : ℕ => criticalPackingBase) atTop
        (nhds criticalPackingBase) := tendsto_const_nhds
  simpa [manuscriptPackingRootError] using! hpacking.sub hconstant
end CohnElkies

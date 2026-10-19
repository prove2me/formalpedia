-- Prove2me | solution 1 for CohnElkies.tendsto_manuscriptBinaryExponentError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/86755566-d82a-47b0-a633-ba4fdc732225

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
    (hbinary : SharpBinaryLogAsymptotic) :
    Tendsto manuscriptBinaryExponentError atTop (nhds (0 : ℝ)) := by
  unfold SharpBinaryLogAsymptotic at hbinary
  have hconstant :
      Tendsto (fun _ : ℕ => criticalBinaryExponent) atTop
        (nhds criticalBinaryExponent) := tendsto_const_nhds
  simpa [manuscriptBinaryExponentError] using! hbinary.neg.sub hconstant
end CohnElkies

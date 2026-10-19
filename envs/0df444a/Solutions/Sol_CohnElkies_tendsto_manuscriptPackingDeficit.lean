-- Prove2me | solution 1 for CohnElkies.tendsto_manuscriptPackingDeficit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/ab8fdc8b-9fc6-462f-bbf9-46d2213222fc

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
    Tendsto manuscriptPackingDeficit atTop (nhds (0 : ℝ)) := by
  unfold SharpPackingRootAsymptotic at hpacking
  have hconstant :
      Tendsto (fun _ : ℕ => criticalPackingBase) atTop
        (nhds criticalPackingBase) := tendsto_const_nhds
  have hsub :
      Tendsto
        (fun d : ℕ =>
          criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹))
        atTop (nhds (0 : ℝ)) := by
    simpa using! hconstant.sub hpacking
  have hmax :=
    (tendsto_const_nhds (f := atTop) (x := (0 : ℝ))).max hsub
  simpa [manuscriptPackingDeficit] using! hmax
end CohnElkies

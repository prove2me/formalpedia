-- Prove2me | solution 2 for CohnElkies.tendsto_manuscriptPackingRootError
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:25:22.522078+00:00
-- url     : https://prove2.me/submissions/fec8f31d-c60f-44a2-8c8f-778e7a9b8418

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


theorem solution
    (hpacking : SharpPackingRootAsymptotic) :
    Tendsto manuscriptPackingRootError atTop (nhds (0 : ℝ)) := by
  have h : Tendsto (fun d : ℕ => (linearProgram d) ^ ((d : ℝ)⁻¹)) atTop (nhds criticalPackingBase) := hpacking
  have := h.sub_const criticalPackingBase
  rw [sub_self] at this
  exact this


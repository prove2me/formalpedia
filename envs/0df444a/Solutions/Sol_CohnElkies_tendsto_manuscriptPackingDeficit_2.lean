-- Prove2me | solution 2 for CohnElkies.tendsto_manuscriptPackingDeficit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:49.288784+00:00
-- url     : https://prove2.me/submissions/90b3e123-311e-465e-b7bd-f43dd9614e7c

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
    Tendsto manuscriptPackingDeficit atTop (nhds (0 : ℝ)) := by
  have h : Tendsto (fun d : ℕ => criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹)) atTop (nhds 0) := by
    have := (tendsto_const_nhds (x := criticalPackingBase)).sub hpacking
    simpa using this
  have := (tendsto_const_nhds (x := (0:ℝ))).max h
  show Tendsto (fun d : ℕ => max 0 (criticalPackingBase - (linearProgram d) ^ ((d : ℝ)⁻¹))) atTop (nhds 0)
  simpa using this


-- Prove2me | solution 2 for CohnElkies.manuscriptPackingDeficit_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:34:10.947308+00:00
-- url     : https://prove2.me/submissions/b0e6558d-4048-4eb4-8ed7-07a6aa249a0e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpAsymptotics
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution :
    Asymptotics.IsLittleO atTop
      manuscriptPackingDeficit (fun _ : ℕ => (1 : ℝ)) := by
  have h : Tendsto (fun d : ℕ => (linearProgram d) ^ ((d : ℝ)⁻¹)) atTop (nhds criticalPackingBase) :=
    CohnElkies.sharpAsymptotics.2.1
  have h2 : Tendsto manuscriptPackingDeficit atTop (nhds (max 0 (criticalPackingBase - criticalPackingBase))) :=
    tendsto_const_nhds.max (tendsto_const_nhds.sub h)
  rw [sub_self, max_self] at h2
  exact (Asymptotics.isLittleO_one_iff ℝ).mpr h2


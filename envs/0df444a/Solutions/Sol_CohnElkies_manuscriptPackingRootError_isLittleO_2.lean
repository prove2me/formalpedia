-- Prove2me | solution 2 for CohnElkies.manuscriptPackingRootError_isLittleO
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:33:50.415736+00:00
-- url     : https://prove2.me/submissions/0d681aee-b465-4318-a650-48274da11b80

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
      manuscriptPackingRootError (fun _ : ℕ => (1 : ℝ)) := by
  have h : Tendsto (fun d : ℕ => (linearProgram d) ^ ((d : ℝ)⁻¹)) atTop (nhds criticalPackingBase) :=
    CohnElkies.sharpAsymptotics.2.1
  have := h.sub_const criticalPackingBase
  rw [sub_self] at this
  exact (Asymptotics.isLittleO_one_iff ℝ).mpr this


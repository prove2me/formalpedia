-- Prove2me | solution 2 for CohnElkies.manuscriptBinaryExponentError_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:33:39.992844+00:00
-- url     : https://prove2.me/submissions/83464a38-5d30-4548-a7a0-419e444b2475

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
    Tendsto manuscriptBinaryExponentError atTop (nhds (0 : ℝ)) := by
  have h : Tendsto (fun d : ℕ => Real.logb 2 (linearProgram d) / (d : ℝ)) atTop (nhds (-criticalBinaryExponent)) :=
    CohnElkies.sharpAsymptotics.2.2.2
  have := (h.neg).sub_const criticalBinaryExponent
  rw [neg_neg, sub_self] at this
  exact this


-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_halfInteger_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:14:49.279242+00:00
-- url     : https://prove2.me/submissions/18723d3f-2206-4248-9ae8-be404d45fff4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_exp_integrable
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution
    {a : ℝ} (ha : 0 < a) (k : ℕ) (R : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y) := by
  have h := CohnElkies.lowerGammaBoundaryLog_dimension_exp_integrable (d := 2 * k + 1) (by omega) ha R
  have e : ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
  rw [e] at h
  exact h


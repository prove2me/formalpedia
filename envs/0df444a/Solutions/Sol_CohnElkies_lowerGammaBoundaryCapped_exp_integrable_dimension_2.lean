-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryCapped_exp_integrable_dimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:14:20.794194+00:00
-- url     : https://prove2.me/submissions/26bb6510-8dc4-4b8a-ab6a-6bdaa7d562f0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_exp_integrable
import Theorems.Thm_CohnElkies_lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology


theorem solution
    {d : ℕ} (hd : 0 < d) {a : ℝ}
    (ha : 0 < a) (R D : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  exact CohnElkies.lowerGammaBoundaryCapped_exp_integrable_of_exp_integrable (by positivity) ha R D
    (CohnElkies.lowerGammaBoundaryLog_dimension_exp_integrable hd ha R)


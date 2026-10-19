-- Prove2me | solution 2 for CohnElkies.upperGammaMeasureDensity_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:26.934721+00:00
-- url     : https://prove2.me/submissions/f3273ca6-30b4-42e4-8803-571ea19a145f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    0 < upperGammaMeasureDensity ℓ η a := by
  unfold upperGammaMeasureDensity
  have h1 : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.2 (by have := div_pos (by linarith : 0 < 2*a) hℓ; linarith)
  have h2 : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by linarith
  positivity


-- Prove2me | solution 2 for CohnElkies.upperGammaDamping_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:21.820296+00:00
-- url     : https://prove2.me/submissions/80e40c82-67c5-4eb3-88d7-8cd2e456b3d1

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
    {ℓ η : ℝ} (hℓ : 0 < ℓ) (T : ℝ) :
    0 ≤ upperGammaDamping ℓ η T := by
  unfold upperGammaDamping
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro a ha
  have ha' : (0:ℝ) < a := ha
  unfold upperGammaDampingIntegrand upperGammaMeasureDensity
  have h1 : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
  have h2 : Real.exp (-(2 * a / ℓ)) < 1 := Real.exp_lt_one_iff.mpr (by have := div_pos (by linarith : (0:ℝ) < 2 * a) hℓ; linarith)
  have h3 : 0 < a * (1 - Real.exp (-(2 * a / ℓ))) := mul_pos ha' (by linarith)
  have := Real.exp_pos (-η * a)
  positivity


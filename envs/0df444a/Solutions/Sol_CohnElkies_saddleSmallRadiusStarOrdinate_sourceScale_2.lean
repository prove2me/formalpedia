-- Prove2me | solution 2 for CohnElkies.saddleSmallRadiusStarOrdinate_sourceScale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:14.208049+00:00
-- url     : https://prove2.me/submissions/902937fd-1b92-4d61-81c5-19f9fc6372e3

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology


theorem solution
    {d : ℕ} (hd : 0 < d) (ε : ℝ)
    {u : ℝ}
    (hu : saddleSmallRadiusStarOrdinate ε d ≤ u) :
    Real.log ((d : ℝ) / 2) / 4 ≤
      ((d : ℝ) / 2) * (1 + u) := by
  have hl : (0:ℝ) < (d:ℝ)/2 := by positivity
  have hu' : -1 + Real.log ((d:ℝ)/2) / (4 * ((d:ℝ)/2)) ≤ u := hu
  have h3 : Real.log ((d:ℝ)/2) / (4 * ((d:ℝ)/2)) ≤ 1 + u := by linarith
  rw [div_le_iff₀ (by positivity)] at h3
  nlinarith


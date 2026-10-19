-- Prove2me | solution 2 for CohnElkies.eventually_saddleSmallRadiusStarOrdinate_gt_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:12:18.692922+00:00
-- url     : https://prove2.me/submissions/f585e461-d302-4ed1-9f82-a9a272e0d1f5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    (ε : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      -1 < saddleSmallRadiusStarOrdinate ε d := by
  filter_upwards [eventually_gt_atTop 2] with d hd
  have h2 : (2:ℝ) < d := by exact_mod_cast hd
  have h1 : 0 < Real.log ((d:ℝ)/2) := Real.log_pos (by rw [lt_div_iff₀ (by norm_num)]; linarith)
  have h3 := div_pos h1 (by positivity : (0:ℝ) < 4 * ((d:ℝ)/2))
  dsimp only [saddleSmallRadiusStarOrdinate]
  linarith


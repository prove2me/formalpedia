-- Prove2me | solution 1 for CohnElkies.eventually_saddleSmallRadiusStarOrdinate_gt_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/d052ec00-c2c9-4240-a79e-5f12e70251c7

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
namespace CohnElkies
theorem _root_.solution
    (ε : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      -1 < saddleSmallRadiusStarOrdinate ε d := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)]
    with d hd
  have hdreal : (3 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd
  have hdimension : 1 < (d : ℝ) / 2 := by
    linarith
  have hlog : 0 < Real.log ((d : ℝ) / 2) :=
    Real.log_pos hdimension
  have hdenominator : 0 < 4 * ((d : ℝ) / 2) := by
    positivity
  have hratio :
      0 < Real.log ((d : ℝ) / 2) /
        (4 * ((d : ℝ) / 2)) :=
    div_pos hlog hdenominator
  unfold saddleSmallRadiusStarOrdinate
  linarith
end CohnElkies

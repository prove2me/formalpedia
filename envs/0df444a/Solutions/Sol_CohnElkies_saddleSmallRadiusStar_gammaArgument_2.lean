-- Prove2me | solution 2 for CohnElkies.saddleSmallRadiusStar_gammaArgument
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:24.637499+00:00
-- url     : https://prove2.me/submissions/25e0c878-2be3-4cce-b02a-f1c9489b25fe

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
    {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    ((d : ℝ) / 2) *
        (1 + saddleSmallRadiusStarOrdinate ε d) / 2 =
      Real.log ((d : ℝ) / 2) / 8 := by
  unfold saddleSmallRadiusStarOrdinate
  have : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  simp only
  field_simp
  ring


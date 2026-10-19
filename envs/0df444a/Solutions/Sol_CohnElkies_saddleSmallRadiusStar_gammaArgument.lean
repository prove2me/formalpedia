-- Prove2me | solution 1 for CohnElkies.saddleSmallRadiusStar_gammaArgument
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/47ec70df-7738-4f54-adae-c5a83950cdb2

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
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    ((d : ℝ) / 2) *
        (1 + saddleSmallRadiusStarOrdinate ε d) / 2 =
      Real.log ((d : ℝ) / 2) / 8 := by
  have hdreal : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd.ne'
  unfold saddleSmallRadiusStarOrdinate
  field_simp
  ring
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.tendsto_saddleResidue_dimension_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/7e531445-8268-4aa0-9095-c018bada438a

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
theorem _root_.solution :
    Tendsto
      (fun d : ℕ => (d : ℝ) / 2)
      atTop atTop := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hmul := hcast.atTop_mul_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  convert! hmul using 1
  funext d
  ring
end CohnElkies

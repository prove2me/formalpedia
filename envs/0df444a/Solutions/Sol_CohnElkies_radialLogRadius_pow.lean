-- Prove2me | solution 1 for CohnElkies.radialLogRadius_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/7f914ec4-df08-44f3-8f71-fd82b646936c

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution {d : ℕ} (hd : 0 < d) (r : ℝ) :
    r ^ d = r * r ^ (d - 1) := by
  have hindex : d - 1 + 1 = d := Nat.sub_add_cancel hd
  conv_lhs => rw [← hindex, pow_succ]
  ring
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_normalizedMellinStrip_top_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/c6d5c076-9b45-433a-be61-a43be95f23f1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_top_norm_le_one

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) (y : ℝ) :
    ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) +
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤ 1 :=
  normalizedRadialMellinStrip_top_norm_le_one
    hd w.function w.radial w.nonzero R y
end CohnElkies

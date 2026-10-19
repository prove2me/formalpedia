-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_normalizedMellinStrip_bottom_norm_le_gamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/6633d615-2c64-415b-9702-de9c9a1d90cf

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_bottom_norm_le_gamma

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
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) (y : ℝ) (hy : y ≠ 0) :
    ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
      Real.exp (lowerGammaBoundaryLog ((d : ℝ) / 2) R y) := by
  simpa [lowerGammaBoundaryLog] using!
    normalizedRadialMellinStrip_bottom_norm_le_gamma
      hd w.function w.radial w.zero_value
      w.anti_fourier w.nonzero R hR y hy
end CohnElkies

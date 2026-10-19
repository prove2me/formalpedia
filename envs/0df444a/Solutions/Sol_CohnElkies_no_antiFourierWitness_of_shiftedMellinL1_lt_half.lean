-- Prove2me | solution 1 for CohnElkies.no_antiFourierWitness_of_shiftedMellinL1_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/9fc089b5-3e66-4038-bad6-37a0eff85855

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_no_antiFourierWitness_of_fourierInversion_lt_half
import Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_shifted_fourier_inversion

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
    (w : AntiFourierWitness d R)
    {a : ℝ} (hapos : 0 < a) (haless : a < (d : ℝ))
    (hsmall :
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hd w.function R
            ((s : ℂ) + Complex.I *
              ((((d : ℝ) / 2 - a : ℝ) : ℂ)))‖) / a <
        (1 / 2 : ℝ)) : False := by
  apply no_antiFourierWitness_of_fourierInversion_lt_half
    hd hR w hapos
    (fun s : ℝ => normalizedRadialMellinStrip hd w.function R
      ((s : ℂ) + Complex.I *
        ((((d : ℝ) / 2 - a : ℝ) : ℂ))))
  · intro v
    exact
      antiFourierWitness_normalizedMellinStrip_shifted_fourier_inversion
        hd hR w haless v
  · exact hsmall
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_normalizedMellinStrip_shifted_fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/42627c60-165d-4b3b-bb4d-95b6d8cac5f9

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_shifted_fourier_inversion

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
    (w : AntiFourierWitness d R) {a : ℝ}
    (ha : a < (d : ℝ)) (v : ℝ) :
    (normalizedRadialLogProfile hd w.function R v : ℂ) =
      (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ =>
          normalizedRadialMellinStrip hd w.function R
            (((2 * Real.pi * ξ : ℝ) : ℂ) +
              Complex.I *
                ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) :
            ℝ → ℂ) v) :=
  normalizedRadialMellinStrip_shifted_fourier_inversion
    hd w.function w.radial w.real w.zero_value hR ha v
end CohnElkies

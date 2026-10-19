-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_normalizedMellinStrip_shifted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/8a653865-aded-4b4a-8d77-36a17364a17a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_shifted_integrable

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
    (ha : a < (d : ℝ)) :
    Integrable (fun t : ℝ =>
      normalizedRadialMellinStrip hd w.function R
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) :=
  normalizedRadialMellinStrip_shifted_integrable
    hd w.function w.real hR ha
end CohnElkies

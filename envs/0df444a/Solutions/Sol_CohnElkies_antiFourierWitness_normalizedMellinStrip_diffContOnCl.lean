-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_normalizedMellinStrip_diffContOnCl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/56e97c12-c1d8-42bb-8551-b3e74d9fb743

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_diffContOnCl

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
    (w : AntiFourierWitness d R) :
    DiffContOnCl ℂ
      (normalizedRadialMellinStrip hd w.function R)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :=
  normalizedRadialMellinStrip_diffContOnCl
    hd w.function w.radial w.zero_value R
end CohnElkies

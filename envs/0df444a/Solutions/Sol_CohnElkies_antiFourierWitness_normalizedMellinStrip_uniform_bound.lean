-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_normalizedMellinStrip_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/ed377bc8-7ca9-4e15-89a4-ceb55c926b50

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_uniform_bound

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
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ,
        -((d : ℝ) / 2) ≤ z.im →
        z.im ≤ (d : ℝ) / 2 →
          ‖normalizedRadialMellinStrip hd w.function R z‖ ≤ C :=
  normalizedRadialMellinStrip_uniform_bound
    hd w.function w.radial w.zero_value R
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.minusSaddleProfile_eq_sourceContourIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/58bdb698-a78f-475a-bed8-9a77a0adfe87

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceMellinContour_integral_change

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ r u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (hu : -1 < u) :
    minusSaddleProfile ε ℓ r =
      ((ℓ / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ T : ℝ,
          saddleMellinInversePower r
              (saddleSourceMellinContour ℓ u T) *
            minusSaddleMellinData ε ℓ
              (saddleSourceMellinContour ℓ u T)) := by
  have ha : 0 < ℓ * (1 + u) := by
    have hη : 0 < 1 + u := by linarith
    positivity
  rw [minusSaddleProfile_eq_positive_contour
    (a := ℓ * (1 + u)) hε hℓ horder hr ha]
  rw [saddleSourceMellinContour_integral_change
    hℓ u (fun z : ℂ =>
      saddleMellinInversePower r z *
        minusSaddleMellinData ε ℓ z)]
  push_cast
  ring
end CohnElkies

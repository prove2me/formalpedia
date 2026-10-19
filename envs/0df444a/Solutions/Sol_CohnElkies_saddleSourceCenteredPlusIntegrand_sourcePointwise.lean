-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredPlusIntegrand_sourcePointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/9c2ab0b8-f78f-4591-a4a5-0f7826d663db

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceMellinContour_shellArgument
import Theorems.Thm_CohnElkies_saddleSourceContour_inversePower_exp
import Theorems.Thm_CohnElkies_saddleSourceContour_envelope_eq_scale_mul_normalized

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
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ) (hu : -1 < u)
    (v T : ℝ) :
    saddleMellinInversePower (Real.exp v)
        (saddleSourceMellinContour ℓ u T) *
      plusSaddleMellinData ε ℓ
        (saddleSourceMellinContour ℓ u T) =
    ((Real.exp (-(ℓ * (1 + u) * v)) *
        saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
      saddleSourceCenteredPlusIntegrand ε ℓ u v T := by
  rw [saddleSourceContour_inversePower_exp,
    plusSaddleMellinData,
    saddleSourceMellinContour_shellArgument hℓ,
    saddleSourceContour_envelope_eq_scale_mul_normalized
      hℓ hu T]
  unfold saddleSourceCenteredPlusIntegrand
    saddleSourceCenteredEnvelope
  push_cast
  ring
end CohnElkies

-- Prove2me | solution 2 for CohnElkies.saddleSourceContourEnvelopeScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:36.614537+00:00
-- url     : https://prove2.me/submissions/45e9607e-6927-4943-a08f-bc82faf2ea3f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace
  SchwartzMap Topology


theorem solution
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u) :
    0 < saddleSourceContourEnvelopeScale ε ℓ u := by
  unfold saddleSourceContourEnvelopeScale
  have h1u : 0 < 1 + u := by linarith
  have hpos : 0 < ℓ * (1 + u) / 2 := by positivity
  have := Real.Gamma_pos_of_pos hpos
  have := Real.exp_pos (-(ℓ * u) * Real.log Real.pi / 2)
  have := Real.exp_pos (ℓ * realHyperbolicShellPhase ε u)
  positivity


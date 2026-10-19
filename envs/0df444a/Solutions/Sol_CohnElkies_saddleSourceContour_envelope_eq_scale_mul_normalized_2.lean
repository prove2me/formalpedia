-- Prove2me | solution 2 for CohnElkies.saddleSourceContour_envelope_eq_scale_mul_normalized
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:44.238124+00:00
-- url     : https://prove2.me/submissions/dc704f69-5cd5-483e-8b1b-dfe5d0f9cbe2

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
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (T : ℝ) :
    saddleMellinEnvelope ε ℓ
        (saddleSourceMellinContour ℓ u T) =
      (saddleSourceContourEnvelopeScale ε ℓ u : ℂ) *
        saddleSourceNormalizedEnvelope ε ℓ u T := by
  have h1u : 0 < 1 + u := by linarith
  have hpos : 0 < ℓ * (1 + u) / 2 := by positivity
  have hS : 0 < saddleSourceContourEnvelopeScale ε ℓ u := by
    unfold saddleSourceContourEnvelopeScale
    have := Real.Gamma_pos_of_pos hpos
    have := Real.exp_pos (-(ℓ * u) * Real.log Real.pi / 2)
    have := Real.exp_pos (ℓ * realHyperbolicShellPhase ε u)
    positivity
  have hS' : (saddleSourceContourEnvelopeScale ε ℓ u : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  unfold saddleSourceNormalizedEnvelope
  field_simp


-- Prove2me | solution 1 for CohnElkies.minusSaddleProfile_exp_eq_centeredIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/e1078b3f-b336-49e2-a202-5fbb21c87def

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceMellinContour_shellArgument
import Theorems.Thm_CohnElkies_minusSaddleProfile_eq_sourceContourIntegral
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
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (v : ℝ) :
    minusSaddleProfile ε ℓ (Real.exp v) =
      (saddleSourceCenteredPrefactor ε ℓ u v : ℂ) *
        (∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) := by
  rw [minusSaddleProfile_eq_sourceContourIntegral
    hε hℓ horder (Real.exp_pos v) hu]
  have hpoint (T : ℝ) :
      saddleMellinInversePower (Real.exp v)
          (saddleSourceMellinContour ℓ u T) *
        minusSaddleMellinData ε ℓ
          (saddleSourceMellinContour ℓ u T) =
      ((Real.exp (-(ℓ * (1 + u) * v)) *
          saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
        saddleSourceCenteredMinusIntegrand ε ℓ u v T := by
    rw [saddleSourceContour_inversePower_exp,
      minusSaddleMellinData,
      saddleSourceMellinContour_shellArgument hℓ,
      saddleSourceContour_envelope_eq_scale_mul_normalized
        hℓ hu T]
    unfold saddleSourceCenteredMinusIntegrand
      saddleSourceCenteredEnvelope
    push_cast
    ring
  have hintegral :
      (∫ T : ℝ,
        saddleMellinInversePower (Real.exp v)
            (saddleSourceMellinContour ℓ u T) *
          minusSaddleMellinData ε ℓ
            (saddleSourceMellinContour ℓ u T)) =
        ((Real.exp (-(ℓ * (1 + u) * v)) *
            saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
          (∫ T : ℝ,
            saddleSourceCenteredMinusIntegrand ε ℓ u v T) := by
    calc
      (∫ T : ℝ,
        saddleMellinInversePower (Real.exp v)
            (saddleSourceMellinContour ℓ u T) *
          minusSaddleMellinData ε ℓ
            (saddleSourceMellinContour ℓ u T)) =
        ∫ T : ℝ,
          ((Real.exp (-(ℓ * (1 + u) * v)) *
              saddleSourceContourEnvelopeScale ε ℓ u : ℝ) : ℂ) *
            saddleSourceCenteredMinusIntegrand ε ℓ u v T := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with T
              exact hpoint T
      _ = _ := integral_const_mul _ _
  rw [hintegral]
  unfold saddleSourceCenteredPrefactor
  push_cast
  ring
end CohnElkies

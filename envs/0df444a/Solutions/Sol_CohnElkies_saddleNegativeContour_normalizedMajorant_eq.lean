-- Prove2me | solution 1 for CohnElkies.saddleNegativeContour_normalizedMajorant_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/80831f3d-4383-4632-a9d1-08cb46b1eee8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleNegativeContour_sourceNormalizationFactor

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ((1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε) /
          saddleOriginValue ε ℓ =
      saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have hb : beta ε ≠ 0 := (beta_pos hε).ne'
  have hΓ : Real.Gamma ((N : ℝ) + 3 / 2) ≠ 0 := by
    apply (Real.Gamma_pos_of_pos (by positivity)).ne'
  have horigin :
      saddleOriginValue ε ℓ =
        2 *
          (Real.exp ((ℓ / 2) * Real.log Real.pi) *
            Real.exp (ℓ * realHyperbolicShellPhase ε 1)) *
          beta ε := by
    unfold saddleOriginValue
    rw [Real.rpow_def_of_pos Real.pi_pos]
    rw [show Real.log Real.pi * (ℓ / 2) =
      (ℓ / 2) * Real.log Real.pi by ring]
    ring
  have hphase := saddleNegativeContour_sourceNormalizationFactor
    ε ℓ N hr
  calc
    ((1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε) /
          saddleOriginValue ε ℓ =
      saddleNegativeRelativeCoefficient ε *
        (r ^ (2 * N + 1) *
          Real.exp
            ((ℓ - saddleTaylorContour N) *
              Real.log Real.pi / 2) *
          Real.exp
            (ℓ * realHyperbolicShellPhase ε
              (saddleNegativeContourOrdinate ℓ N)) /
          (Real.exp ((ℓ / 2) * Real.log Real.pi) *
            Real.exp (ℓ * realHyperbolicShellPhase ε 1))) /
          Real.Gamma ((N : ℝ) + 3 / 2) := by
        rw [horigin]
        unfold saddleNegativeMellinMajorantCoefficient
          saddleNegativeRelativeCoefficient
        field_simp [Real.pi_pos.ne', hb, hΓ,
          (Real.exp_pos ((ℓ / 2) * Real.log Real.pi)).ne',
          (Real.exp_pos
            (ℓ * realHyperbolicShellPhase ε 1)).ne']; ring
    _ = saddleNegativeRelativeCoefficient ε *
        (Real.sqrt (saddleSmallRadiusVariable ε r) *
          saddleSmallRadiusVariable ε r ^ N *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N)) /
          Real.Gamma ((N : ℝ) + 3 / 2) := by
        rw [hphase]
    _ = saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
        ring
end CohnElkies

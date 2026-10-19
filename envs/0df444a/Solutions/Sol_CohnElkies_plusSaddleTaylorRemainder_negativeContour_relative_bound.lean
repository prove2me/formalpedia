-- Prove2me | solution 1 for CohnElkies.plusSaddleTaylorRemainder_negativeContour_relative_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/877c3c9b-b9eb-4ce4-8f6f-31e55fff40b7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusSaddleTaylorRemainder_negativeContour_bound
import Theorems.Thm_CohnElkies_saddleNegativeContour_normalizedMajorant_eq

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
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    {r : ℝ} (hr : 0 < r) :
    ‖plusSaddleTaylorRemainder ε ℓ N r /
      (saddleOriginValue ε ℓ : ℂ)‖ ≤
      saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have hO := saddleOriginValue_pos hε ℓ
  have hraw := plusSaddleTaylorRemainder_negativeContour_bound
    hε hεsmall hℓ N hN horder hmargin hr
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hO]
  calc
    ‖plusSaddleTaylorRemainder ε ℓ N r‖ /
        saddleOriginValue ε ℓ ≤
      ((1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
        saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMass ε) /
            saddleOriginValue ε ℓ := by
        exact (div_le_div_iff_of_pos_right hO).mpr hraw
    _ = saddleNegativeRelativeCoefficient ε *
        Real.sqrt (saddleSmallRadiusVariable ε r) *
        saddleSmallRadiusVariable ε r ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N) :=
      saddleNegativeContour_normalizedMajorant_eq hε ℓ N hr.le
end CohnElkies

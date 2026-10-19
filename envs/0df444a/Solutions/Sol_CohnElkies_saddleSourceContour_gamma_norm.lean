-- Prove2me | solution 1 for CohnElkies.saddleSourceContour_gamma_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/c7c09c62-a2e4-4df1-ac1d-3cf06078a974

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceMellinContour_gammaArgument
import Theorems.Thm_CohnElkies_upperGammaShifted_modulus_eq_exp_neg_damping

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
    {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (T : ℝ) :
    ‖Complex.Gamma
      (saddleSourceMellinContour ℓ u T / 2)‖ =
      Real.Gamma (ℓ * (1 + u) / 2) *
        Real.exp (-upperGammaDamping ℓ (1 + u) T) := by
  rw [saddleSourceMellinContour_gammaArgument]
  exact upperGammaShifted_modulus_eq_exp_neg_damping
    hℓ (by linarith) T
end CohnElkies

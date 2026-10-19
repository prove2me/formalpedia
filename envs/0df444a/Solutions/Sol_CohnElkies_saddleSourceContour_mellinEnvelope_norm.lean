-- Prove2me | solution 1 for CohnElkies.saddleSourceContour_mellinEnvelope_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/cb2b45e1-f19e-4b05-8fa3-0979932bfc86

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceContour_piExponential_norm
import Theorems.Thm_CohnElkies_saddleSourceContour_gamma_norm
import Theorems.Thm_CohnElkies_saddleSourceContour_shellExponential_norm

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
    (T : ℝ) :
    ‖saddleMellinEnvelope ε ℓ
        (saddleSourceMellinContour ℓ u T)‖ =
      saddleSourceContourEnvelopeScale ε ℓ u *
        Real.exp (-saddleSourceContourDamping ε ℓ u T) := by
  have hπ := saddleSourceContour_piExponential_norm ℓ u T
  have hΓ := saddleSourceContour_gamma_norm hℓ hu T
  have hshell := saddleSourceContour_shellExponential_norm
    hε hℓ horder (u := u) T
  have hexp :
      Real.exp (-upperGammaDamping ℓ (1 + u) T) *
          Real.exp
            (-(positiveShellDamping ε ℓ (u - 1) T -
              upperShortShellDamping ε ℓ (u - 1) T)) =
        Real.exp (-saddleSourceContourDamping ε ℓ u T) := by
    rw [← Real.exp_add]
    congr 1
    unfold saddleSourceContourDamping
    ring
  unfold saddleMellinEnvelope
  rw [norm_mul, norm_mul, hπ, hΓ, hshell]
  unfold saddleSourceContourEnvelopeScale
  rw [← hexp]
  ring
end CohnElkies

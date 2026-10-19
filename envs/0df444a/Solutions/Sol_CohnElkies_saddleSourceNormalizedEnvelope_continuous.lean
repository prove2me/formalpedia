-- Prove2me | solution 1 for CohnElkies.saddleSourceNormalizedEnvelope_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/6a516a9a-db2d-4722-90be-ba1e6d954c71

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleRegularMellinFactor_continuous

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    Continuous (saddleSourceNormalizedEnvelope ε ℓ u) := by
  have harg : Continuous
      (fun T : ℝ => saddleSourceMellinContour ℓ u T) := by
    unfold saddleSourceMellinContour
    fun_prop
  have hgamma : Continuous
      (fun T : ℝ =>
        Complex.Gamma (saddleSourceMellinContour ℓ u T / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro T
    have hre :
        0 < (saddleSourceMellinContour ℓ u T).re := by
      unfold saddleSourceMellinContour
      simp
      nlinarith [mul_pos hℓ (show 0 < 1 + u by linarith)]
    exact (saddleMellinGamma_differentiableAt_of_re_pos
      hre).continuousAt.comp_of_eq harg.continuousAt (by rfl)
  have hregular : Continuous
      (fun T : ℝ =>
        saddleRegularMellinFactor ε ℓ
          (saddleSourceMellinContour ℓ u T)) :=
    (saddleRegularMellinFactor_continuous
      hε horder ℓ).comp harg
  have henvelope : Continuous
      (fun T : ℝ =>
        saddleMellinEnvelope ε ℓ
          (saddleSourceMellinContour ℓ u T)) := by
    apply (hgamma.mul hregular).congr
    intro T
    change
      Complex.Gamma (saddleSourceMellinContour ℓ u T / 2) *
          saddleRegularMellinFactor ε ℓ
            (saddleSourceMellinContour ℓ u T) =
        saddleMellinEnvelope ε ℓ
          (saddleSourceMellinContour ℓ u T)
    unfold saddleMellinEnvelope saddleRegularMellinFactor
    ring
  unfold saddleSourceNormalizedEnvelope
  exact henvelope.div_const _
end CohnElkies

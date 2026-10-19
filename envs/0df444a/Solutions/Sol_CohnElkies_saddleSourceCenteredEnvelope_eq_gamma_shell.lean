-- Prove2me | solution 1 for CohnElkies.saddleSourceCenteredEnvelope_eq_gamma_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/4b8c25a5-5dae-439b-9893-d994dbce8ae0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceMellinContour_shellArgument
import Theorems.Thm_CohnElkies_saddleSourceMellinContour_gammaArgument
import Theorems.Thm_CohnElkies_saddleSourceContour_piExponential_eq
import Theorems.Thm_CohnElkies_saddleSourceContour_shellExponential_eq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (v T : ℝ) :
    saddleSourceCenteredEnvelope ε ℓ u v T =
      (Complex.Gamma
          (((ℓ * (1 + u) / 2 : ℝ) : ℂ) -
            Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) /
        (Real.Gamma (ℓ * (1 + u) / 2) : ℂ)) *
      Complex.exp
        ((ℓ : ℂ) *
          (mellinShellPhase ε
              ((T : ℂ) + Complex.I * (u : ℂ)) -
            (realHyperbolicShellPhase ε u : ℂ))) *
      (Complex.exp
        (Complex.I *
          ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) *
        Complex.exp
          (Complex.I * ((ℓ * T * v : ℝ) : ℂ))) := by
  have hη : 0 < 1 + u := by linarith
  have hm : 0 < ℓ * (1 + u) / 2 := by positivity
  have hG :
      (Real.Gamma (ℓ * (1 + u) / 2) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (Real.Gamma_pos_of_pos hm).ne'
  have hπ :
      (Real.exp (-(ℓ * u) * Real.log Real.pi / 2) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hs :
      (Real.exp (ℓ * realHyperbolicShellPhase ε u) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  unfold saddleSourceCenteredEnvelope
    saddleSourceNormalizedEnvelope saddleMellinEnvelope
    saddleSourceContourEnvelopeScale
  rw [saddleSourceMellinContour_shellArgument hℓ,
    saddleSourceMellinContour_gammaArgument,
    saddleSourceContour_piExponential_eq,
    saddleSourceContour_shellExponential_eq]
  push_cast
  field_simp [hπ, hG, hs]
end CohnElkies

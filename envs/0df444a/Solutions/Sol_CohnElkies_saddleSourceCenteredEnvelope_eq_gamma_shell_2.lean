-- Prove2me | solution 2 for CohnElkies.saddleSourceCenteredEnvelope_eq_gamma_shell
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:04:20.761665+00:00
-- url     : https://prove2.me/submissions/bafdd54d-e673-43cf-b613-00aec939abf5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
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
  have hℓ0 : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hpos : 0 < ℓ * (1 + u) / 2 := by nlinarith
  have hΓ : (Real.Gamma (ℓ * (1 + u) / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos hpos).ne'
  unfold saddleSourceCenteredEnvelope saddleSourceNormalizedEnvelope saddleMellinEnvelope
    saddleSourceContourEnvelopeScale saddleSourceMellinContour
  have hz : Complex.I * ((((ℓ * (1 + u) : ℝ) : ℂ) - Complex.I * ((ℓ * T : ℝ) : ℂ)) - (ℓ : ℂ)) / (ℓ : ℂ)
      = (T : ℂ) + Complex.I * (u : ℂ) := by
    rw [div_eq_iff hℓ0]
    push_cast
    linear_combination (-(ℓ : ℂ) * (T : ℂ)) * Complex.I_sq
  have hg : (((ℓ * (1 + u) : ℝ) : ℂ) - Complex.I * ((ℓ * T : ℝ) : ℂ)) / 2 =
      (((ℓ * (1 + u) / 2 : ℝ) : ℂ) - Complex.I * ((ℓ * T / 2 : ℝ) : ℂ)) := by
    push_cast; ring
  have hA : Complex.exp (((ℓ : ℂ) - (((ℓ * (1 + u) : ℝ) : ℂ) - Complex.I * ((ℓ * T : ℝ) : ℂ))) *
      (Real.log Real.pi : ℂ) / 2) =
      Complex.exp (Complex.I * ((ℓ * T * Real.log Real.pi / 2 : ℝ) : ℂ)) *
        ((Real.exp (-(ℓ * u) * Real.log Real.pi / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast; ring
  have hE : Complex.exp ((ℓ : ℂ) * (mellinShellPhase ε ((T : ℂ) + Complex.I * (u : ℂ)) -
      (realHyperbolicShellPhase ε u : ℂ))) =
      Complex.exp ((ℓ : ℂ) * mellinShellPhase ε ((T : ℂ) + Complex.I * (u : ℂ))) /
        ((Real.exp (ℓ * realHyperbolicShellPhase ε u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_sub]
    congr 1
    push_cast; ring
  rw [hz, hg, hA, hE]
  have h1 : ((Real.exp (-(ℓ * u) * Real.log Real.pi / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have h2 : ((Real.exp (ℓ * realHyperbolicShellPhase ε u) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  push_cast
  push_cast at h1 h2 hΓ
  field_simp


-- Prove2me | solution 1 for CohnElkies.upperNegativeContour_gamma_mul_shellExponential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/0e7238cd-97cc-432d-bf13-f57086257e01

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_realHyperbolicShellPhase_neg
import Theorems.Thm_CohnElkies_positiveShellDamping_nonneg
import Theorems.Thm_CohnElkies_norm_saddleShellExponential_eq_exp_neg_damping
import Theorems.Thm_CohnElkies_upperNegativeContour_gamma_mul_exp_short_le
import Theorems.Thm_CohnElkies_upperShortShellDamping_neg_frequency
import Theorems.Thm_CohnElkies_saddleTaylorContour_gammaArgument
import Theorems.Thm_CohnElkies_saddleTaylorContour_shellArgument

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
    (s : ℝ) :
    ‖Complex.Gamma
        (((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I) / 2) *
      Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          (Complex.I *
            (((saddleTaylorContour N : ℂ) +
              (s : ℂ) * Complex.I) - (ℓ : ℂ)) /
                (ℓ : ℂ)))‖ ≤
      Real.exp
        (ℓ * realHyperbolicShellPhase ε
          (saddleNegativeContourOrdinate ℓ N)) *
        ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp (2 * ε * Real.log 2) *
            Real.exp (-ε * Real.pi * |s|)) := by
  let κ : ℝ := saddleNegativeContourOrdinate ℓ N
  let T : ℝ := -s / ℓ
  let δ : ℝ := -κ - 1
  let S : ℝ := upperShortShellDamping ε ℓ δ T
  let P : ℝ := positiveShellDamping ε ℓ δ T
  have hP : 0 ≤ P := positiveShellDamping_nonneg hℓ.le
  have hgamma := upperNegativeContour_gamma_mul_exp_short_le
    hε hεsmall hℓ N hN horder hmargin (-s)
  have heven :
      upperShortShellDamping ε ℓ δ (-(-s) / ℓ) = S := by
    have h := upperShortShellDamping_neg_frequency
      ε ℓ δ T
    have hfreq : -T = -(-s) / ℓ := by
      try dsimp [T]
      ring
    rw [hfreq] at h
    exact h
  have hgamma' :
      ‖Complex.Gamma
        (upperNegativeHalfGammaArgument N (-s))‖ *
          Real.exp S ≤
        (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp (2 * ε * Real.log 2) *
            Real.exp (-ε * Real.pi * |s|) := by
    have h :
        ‖Complex.Gamma
          (upperNegativeHalfGammaArgument N (-s))‖ *
            Real.exp
              (upperShortShellDamping ε ℓ δ (s / ℓ)) ≤
          (Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
            Real.exp (2 * ε * Real.log 2) *
              Real.exp (-ε * Real.pi * |s|) := by
      simpa [κ, δ, abs_neg] using! hgamma
    have hfreq : s / ℓ = -T := by
      try dsimp [T]
      ring
    rw [hfreq, upperShortShellDamping_neg_frequency] at h
    exact h
  have hshell := norm_saddleShellExponential_eq_exp_neg_damping
    hε horder ℓ T (-κ)
  have hshell' :
      ‖Complex.exp
        ((ℓ : ℂ) * mellinShellPhase ε
          ((T : ℂ) + Complex.I * ((-κ : ℝ) : ℂ)))‖ =
        Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
          Real.exp (-(P - S)) := by
    rw [realHyperbolicShellPhase_neg] at hshell
    convert! hshell using 1
  have hexp : Real.exp (-(P - S)) ≤ Real.exp S := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [saddleTaylorContour_gammaArgument,
    saddleTaylorContour_shellArgument hℓ N s,
    norm_mul, hshell']
  calc
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
        (Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
          Real.exp (-(P - S))) ≤
      ‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
        (Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
          Real.exp S) := by
        gcongr
    _ = Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
        (‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
          Real.exp S) := by ring
    _ ≤ Real.exp (ℓ * realHyperbolicShellPhase ε κ) *
        ((Real.pi / Real.Gamma ((N : ℝ) + 3 / 2)) *
          Real.exp (2 * ε * Real.log 2) *
            Real.exp (-ε * Real.pi * |s|)) :=
      mul_le_mul_of_nonneg_left hgamma' (Real.exp_pos _).le
end CohnElkies

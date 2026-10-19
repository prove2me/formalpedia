-- Prove2me | solution 1 for CohnElkies.normalizedRadialMellinStrip_shifted_fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/8346b9e7-235e-49a5-adfb-2d77e9115544

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_weighted_ofReal
import Theorems.Thm_CohnElkies_normalizedRadialMellinStrip_shifted_eq_fourier
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_weighted_integrable
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_weighted_fourier_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hreal : IsRealValued f)
    (hzero : f (0 : Euclidean d) = 0)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ)) (v : ℝ) :
    (normalizedRadialLogProfile hd f R v : ℂ) =
      (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ =>
          normalizedRadialMellinStrip hd f R
            (((2 * Real.pi * ξ : ℝ) : ℂ) +
              Complex.I *
                ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) :
            ℝ → ℂ) v) := by
  let W : ℝ → ℂ := fun u =>
    (Real.exp (-a * u) : ℂ) *
      (normalizedRadialLogProfile hd f R u : ℂ)
  let κ : ℝ := (d : ℝ) - a
  let g : 𝓢(ℝ, ℂ) := radialSchwartzProfile hd f
  let c : ℂ :=
    ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ)
  have hW : Integrable W := by
    try dsimp [W]
    apply normalizedRadialLogProfile_weighted_integrable
      hd f hf hreal hzero hR
    linarith
  have hFW : Integrable (𝓕 W : ℝ → ℂ) := by
    try dsimp [W]
    exact normalizedRadialLogProfile_weighted_fourier_integrable
      hd f hreal hR ha
  have hweight :
      W = (fun u : ℝ =>
        c * schwartzExponentialTilt g κ R u) := by
    funext u
    try dsimp [W]
    rw [normalizedRadialLogProfile_weighted_ofReal
      hd f hreal R a u]
    simp [c, g, κ, schwartzExponentialTilt]
    ring
  have hcontinuous : Continuous W := by
    rw [hweight]
    exact
      (schwartzExponentialTilt_differentiable
        g κ R).continuous.const_mul c
  have hfrequency :
      (fun ξ : ℝ =>
        normalizedRadialMellinStrip hd f R
          (((2 * Real.pi * ξ : ℝ) : ℂ) +
            Complex.I *
              ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) =
        (𝓕 W : ℝ → ℂ) := by
    funext ξ
    rw [normalizedRadialMellinStrip_shifted_eq_fourier
      hd f hreal R hR a (2 * Real.pi * ξ)]
    change
      (𝓕 W : ℝ → ℂ)
          ((2 * Real.pi * ξ) / (2 * Real.pi)) =
        (𝓕 W : ℝ → ℂ) ξ
    field_simp [Real.pi_ne_zero]
  have hinversion :
      (𝓕⁻ (𝓕 W : ℝ → ℂ) : ℝ → ℂ) v = W v :=
    hW.fourierInv_fourier_eq hFW hcontinuous.continuousAt
  have hcancel :
      (Real.exp (a * v) : ℂ) * W v =
        (normalizedRadialLogProfile hd f R v : ℂ) := by
    try dsimp [W]
    rw [← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    have hsum : a * v + -a * v = 0 := by ring
    rw [hsum, Real.exp_zero]
    norm_num
  calc
    (normalizedRadialLogProfile hd f R v : ℂ) =
        (Real.exp (a * v) : ℂ) * W v := hcancel.symm
    _ = (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ =>
          normalizedRadialMellinStrip hd f R
            (((2 * Real.pi * ξ : ℝ) : ℂ) +
              Complex.I *
                ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) :
            ℝ → ℂ) v) := by
      rw [hfrequency, hinversion]
end CohnElkies

-- Prove2me | solution 1 for CohnElkies.normalizedRadialLogProfile_weighted_fourier_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/7f0429d6-e23b-4b55-8a19-d838c6945276

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedRadialLogProfile_weighted_ofReal

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
    (hreal : IsRealValued f)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ)) :
    Integrable
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
        ℝ → ℂ) := by
  let κ : ℝ := (d : ℝ) - a
  let g : 𝓢(ℝ, ℂ) := radialSchwartzProfile hd f
  let c : ℂ :=
    ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ)
  have hκ : 0 < κ := by
    try dsimp [κ]
    linarith
  have hweight :
      (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) =
        (fun v : ℝ =>
          c * schwartzExponentialTilt g κ R v) := by
    funext v
    rw [normalizedRadialLogProfile_weighted_ofReal
      hd f hreal R a v]
    simp [c, g, κ, schwartzExponentialTilt]
    ring
  have hfourier :=
    (schwartzExponentialTilt_fourier_integrable
      g hκ hR).const_mul c
  have hscalar (t : ℝ) :
      (𝓕 (fun v : ℝ =>
        c * schwartzExponentialTilt g κ R v) :
        ℝ → ℂ) t =
        c *
          (𝓕 (schwartzExponentialTilt g κ R) :
            ℝ → ℂ) t := by
    rw [Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    ring
  apply hfourier.congr
  filter_upwards [] with t
  rw [hweight]
  exact (hscalar t).symm
end CohnElkies

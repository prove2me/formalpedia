-- Prove2me | solution 1 for CohnElkies.poissonLogistic_characteristic_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/fe578c69-4fda-4eb7-87a3-e70496995063

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogistic_betaIntegral
import Theorems.Thm_CohnElkies_gamma_one_add_imaginary_mul_gamma_one_sub

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {t : ℝ} (ht : t ≠ 0) :
    (∫ u : ℝ,
      (poissonLogisticDensity u : ℂ) *
        Complex.exp
          (Complex.I * (t : ℂ) * (u : ℂ))) =
      ((t / Real.sinh t : ℝ) : ℂ) := by
  let x : ℝ := t / Real.pi
  have hx : x ≠ 0 := by
    try dsimp [x]
    exact div_ne_zero ht Real.pi_ne_zero
  let w : ℂ := Complex.I * (x : ℂ)
  have hwplus : 0 < (1 + w).re := by
    try dsimp [w]
    norm_num
  have hwminus : 0 < (1 - w).re := by
    try dsimp [w]
    norm_num
  have hphase (u : ℝ) :
      ((Real.pi * u : ℝ) : ℂ) * w =
        Complex.I * (t : ℂ) * (u : ℂ) := by
    try dsimp [w, x]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hbeta :
      Complex.betaIntegral (1 + w) (1 - w) =
        Complex.Gamma (1 + w) *
          Complex.Gamma (1 - w) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div
      (1 + w) (1 - w) hwplus hwminus]
    have hsum : (1 + w) + (1 - w) = (2 : ℂ) := by
      ring
    rw [hsum]
    norm_num
  have hscale : Real.pi * x = t := by
    try dsimp [x]
    field_simp [Real.pi_ne_zero]
  calc
    (∫ u : ℝ,
      (poissonLogisticDensity u : ℂ) *
        Complex.exp
          (Complex.I * (t : ℂ) * (u : ℂ))) =
        Complex.betaIntegral (1 + w) (1 - w) := by
      rw [poissonLogistic_betaIntegral w]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [hphase]
    _ = Complex.Gamma (1 + w) *
          Complex.Gamma (1 - w) := hbeta
    _ = ((Real.pi * x / Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
      exact gamma_one_add_imaginary_mul_gamma_one_sub hx
    _ = ((t / Real.sinh t : ℝ) : ℂ) := by
      rw [hscale]
end CohnElkies

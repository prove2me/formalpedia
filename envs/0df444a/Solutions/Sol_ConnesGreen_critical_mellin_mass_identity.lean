-- Prove2me | solution 1 for ConnesGreen.critical_mellin_mass_identity
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T20:04:38.692977+00:00
-- url     : https://prove2.me/submissions/59661643-db56-45b8-9027-6430d2f45a91

import Definitions.Def_ConnesRZ_weil_defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ
open scoped FourierTransform
noncomputable section

private theorem mellin_fourier_dictionary (g : ℝ → ℂ) (r : ℝ) :
    mellinHat g (1 / 2 + I * r) = 𝓕 g (-r / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold mellinHat
  simp only [add_sub_cancel_left]
  congr 1
  ext u
  rw [smul_eq_mul, mul_comm (g u)]
  congr 1
  have h : (-2 * Real.pi * u * (-r / (2 * Real.pi))) = r * u := by field_simp
  rw [h]
  push_cast
  ring

/-- Exact original 2 pi Fourier mass normalization, with no extra integrability premise. -/
theorem solution (g : ℝ → ℂ) (hg : IsTest g) :
    (∫ r : ℝ, ‖mellinHat g (1 / 2 + I * r)‖ ^ 2) =
      2 * Real.pi * (∫ s : ℝ, ‖g s‖ ^ 2) := by
  let f := hg.2.toSchwartzMap (hg.1.of_le (by simp))
  have hp := SchwartzMap.integral_norm_sq_fourier f
  have hp' : (∫ r : ℝ, ‖𝓕 g r‖ ^ 2) = ∫ s : ℝ, ‖g s‖ ^ 2 := by
    rw [SchwartzMap.fourier_coe] at hp
    exact hp
  have he : (fun r : ℝ => ‖mellinHat g (1 / 2 + I * r)‖ ^ 2) =
      fun r => (fun u : ℝ => ‖𝓕 g u‖ ^ 2) (-(1 / (2 * Real.pi)) * r) := by
    ext r
    rw [mellin_fourier_dictionary]
    congr 2
    ring
  rw [he]
  rw [Measure.integral_comp_mul_left (fun u : ℝ => ‖𝓕 g u‖ ^ 2) (-(1 / (2 * Real.pi)))]
  have habs : |(-(1 / (2 * Real.pi)) : ℝ)⁻¹| = 2 * Real.pi := by
    rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)]
  rw [habs, smul_eq_mul, hp']

-- Prove2me | solution 1 for ConnesGreen.critical_mellin_density_integrable
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T03:01:25.371144+00:00
-- url     : https://prove2.me/submissions/9c322e45-ed40-4e9a-9096-9517b4d9a928

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

theorem solution (g : ℝ → ℂ) (hg : IsTest g) :
    Integrable (fun r : ℝ => ‖mellinHat g (1/2 + I*r)‖ ^ 2) := by
  let f := hg.2.toSchwartzMap (hg.1.of_le (by simp))
  have hd := (𝓕 f : SchwartzMap ℝ ℂ).memLp 2
  have hi := hd.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [SchwartzMap.fourier_coe] at hi
  have hc := hi.comp_mul_left' (R := (-(1/(2*Real.pi)) : ℝ)) (by exact neg_ne_zero.mpr (div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) Real.pi_ne_zero)))
  convert hc using 1
  ext r
  change ‖mellinHat g (1/2 + I*r)‖ ^ 2 = ‖𝓕 g (-(1/(2*Real.pi))*r)‖ ^ 2
  rw [mellin_fourier_dictionary]
  congr 2
  ring


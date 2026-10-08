-- Prove2me | solution 1 for ConnesGreen.RG0Integration.critical_mellin_low_mass_fraction
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:48:31.441593+00:00
-- url     : https://prove2.me/submissions/affca6d0-00e3-4033-8c16-e90d4ab9005f

import Theorems.Thm_ConnesGreen_supported_mellin_norm_sq_mass_bound
import Theorems.Thm_ConnesGreen_critical_mellin_mass_identity
import Definitions.Def_ConnesGreen_canonical_model
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesGreen WeilDefect.ConnesNative Set
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

private theorem density_integrable (g : ℝ → ℂ) (hg : IsTest g) :
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

theorem solution (B T : ℝ)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (g : ℝ → ℂ) (hg : SupportedTest T g) :
    (∫ r in Icc (-B) B, ‖mellinHat g (1/2 + I*r)‖ ^ 2) ≤
      (2 * B * T / Real.pi) * (∫ r : ℝ, ‖mellinHat g (1/2 + I*r)‖ ^ 2) := by
  have hd := (density_integrable g hg.1).integrableOn (s := Icc (-B) B)
  have hb : ∀ r : ℝ, ‖mellinHat g (1/2 + I*r)‖ ^ 2 ≤
      2*T*(∫ s : ℝ, ‖g s‖ ^ 2) := by
    intro r
    simpa using supported_mellin_norm_sq_mass_bound T hT g hg (1/2 + I*r)
  have hi := setIntegral_mono_on hd (integrableOn_const (by simp [Real.volume_Icc]))
    measurableSet_Icc (fun r _ => hb r)
  rw [setIntegral_const] at hi
  have hv : volume.real (Icc (-B) B) = 2*B := by
    simp [Real.volume_real_Icc, sub_neg_eq_add, ← two_mul,
      max_eq_left (by positivity : 0 ≤ 2*B)]
  rw [hv, smul_eq_mul] at hi
  rw [critical_mellin_mass_identity g hg.1]
  calc
    _ ≤ 4*B*T*(∫ s : ℝ, ‖g s‖ ^ 2) := by nlinarith [hi]
    _ = _ := by field_simp; ring

-- Prove2me | solution 1 for ConnesGreen.arch_convolution_re_eq_gamma_density
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T03:02:46.102766+00:00
-- url     : https://prove2.me/submissions/d4067962-61f1-4ef7-bd81-ed2e0dcdb012

import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
open Complex MeasureTheory ConnesRZ
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem solution (g : ℝ → ℂ) (hg : IsTest g) :
    (archTerm (conv g (starInv g))).re = (1 / (2 * Real.pi)) *
      ∫ r : ℝ, ‖mellinHat g (1 / 2 + I * r)‖ ^ 2 *
        ((Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi) := by 
  have hc : ∀ r : ℝ, mellinHat (conv g (starInv g)) (1 / 2 + I * r) =
      ((‖mellinHat g (1 / 2 + I * r)‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [ConnesRZ.mellinHat_conv_starInv g hg]
    have he : (1 : ℂ) - (starRingEnd ℂ) (1 / 2 + I * r) = 1 / 2 + I * r := by
      apply Complex.ext <;> simp <;> ring
    rw [he, Complex.mul_conj']
    push_cast
    rfl
  unfold archTerm
  simp_rw [hc, ← Complex.digamma_def, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  have e : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  rw [e, ← Complex.ofReal_mul, Complex.ofReal_re]

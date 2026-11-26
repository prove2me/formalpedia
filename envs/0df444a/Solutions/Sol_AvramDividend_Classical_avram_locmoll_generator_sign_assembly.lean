-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_generator_sign_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:39:18.4999+00:00
-- url     : https://prove2.me/submissions/8aad9722-1e21-432a-8e38-beada7d60783

import Mathlib
open MeasureTheory Filter
set_option autoImplicit false
theorem solution
    (a b q : ℝ) (A B J W : ℝ → ℝ)
    (hA : Integrable A) (hB : Integrable B)
    (hJ : Integrable J) (hW : Integrable W)
    (hsign : ∀ᵐ r ∂volume, a * A r + b * B r + J r - q * W r ≤ 0) :
    a * (∫ r, A r) + b * (∫ r, B r) + (∫ r, J r) -
      q * (∫ r, W r) ≤ 0 := by 
  have h := integral_nonpos_of_ae hsign
  have hAB : Integrable (fun r => a * A r + b * B r) :=
    (hA.const_mul a).add (hB.const_mul b)
  calc
    _ = (∫ r, a * A r + b * B r) + (∫ r, J r) -
        (∫ r, q * W r) := by
      rw [integral_add (hA.const_mul a) (hB.const_mul b)]
      simp only [integral_const_mul]
    _ = (∫ r, (a * A r + b * B r) + J r) -
        (∫ r, q * W r) := by rw [integral_add hAB hJ]
    _ = (∫ r, a * A r + b * B r + J r - q * W r) := by
      exact (integral_sub (hAB.add hJ) (hW.const_mul q)).symm
    _ ≤ 0 := h

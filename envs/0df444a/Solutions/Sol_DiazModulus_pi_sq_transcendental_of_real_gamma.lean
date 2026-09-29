-- Prove2me | solution 1 for DiazModulus.pi_sq_transcendental_of_real_gamma
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T19:52:24.395952+00:00
-- url     : https://prove2.me/submissions/5d673930-28b9-4393-946f-efe7c78048fe

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

-- Exact submission bytes for the planned `/verify` call (top-level
-- `theorem solution`, no namespace wrapper, helpers inlined). This file is
-- the local verification gate; the submitted file must be byte-identical
-- apart from this comment header.
theorem solution
    (hS : ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.im = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) :
    Transcendental ℚ ((((Real.pi : ℝ) : ℂ)) ^ 2) := by
  have XX_alg_neg : ∀ {z : ℂ}, IsAlgebraic ℚ z → IsAlgebraic ℚ (-z) := by
    intro z hz
    rw [← DiazModulus.mem_Qbar_iff] at *
    exact Subfield.neg_mem _ hz
  intro hpi2
  have hpi0 : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hγ : IsAlgebraic ℚ ((((Real.pi ^ 2 : ℝ))) : ℂ) := by
    have hcast : ((((Real.pi ^ 2) : ℝ)) : ℂ) = (((Real.pi : ℝ) : ℂ)) ^ 2 := by
      push_cast
      ring
    rw [hcast]
    exact hpi2
  have hγ0 : ((((Real.pi ^ 2 : ℝ))) : ℂ) ≠ 0 := by
    have hne : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
    exact_mod_cast hne
  have him : ((((Real.pi ^ 2 : ℝ))) : ℂ).im = 0 := Complex.ofReal_im _
  have hcon := hS _ hγ hγ0 him
  have hlam : ((((Real.pi ^ 2 : ℝ))) : ℂ) / (((Real.pi : ℝ) : ℂ) * Complex.I) =
      -(((Real.pi : ℝ) : ℂ) * Complex.I) := by
    have hI2 : Complex.I ^ 2 = (-1 : ℂ) := by rw [sq, Complex.I_mul_I]
    rw [div_eq_iff (mul_ne_zero hpi0 Complex.I_ne_zero)]
    push_cast
    ring_nf
    rw [hI2]
    ring
  rw [hlam, Complex.exp_neg_pi_mul_I] at hcon
  exact hcon (XX_alg_neg isAlgebraic_one)

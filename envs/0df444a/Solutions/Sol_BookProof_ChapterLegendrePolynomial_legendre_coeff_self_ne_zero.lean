-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.legendre_coeff_self_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:33:11.192873+00:00
-- url     : https://prove2.me/submissions/3fd29304-aed3-40cb-b8a6-cd350984d8b4

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.legendre_coeff_self_ne_zero
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendreAux_coeff_self
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) : (legendre l).coeff l ≠ 0 := by

  rw [legendre, coeff_C_mul, legendreAux_coeff_self]
  have h1 : ((2 * l).descFactorial l : ℝ) ≠ 0 := by
    have h : (2 * l).descFactorial l ≠ 0 := by
      have := Nat.descFactorial_eq_zero_iff_lt (n := 2 * l) (k := l)
      omega
    exact_mod_cast h
  have h2 : ((2 : ℝ) ^ l * (Nat.factorial l : ℝ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    positivity
  exact mul_ne_zero h2 h1

-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_top_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:33:22.949011+00:00
-- url     : https://prove2.me/submissions/459316f6-d02e-4244-a0b8-40da11c40235

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_top_ne_zero
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_coeff_self_ne_zero
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (l μ : ℕ) (h : μ ≤ l) :
    (derivative^[μ] (legendre l)).coeff (l - μ) ≠ 0 := by

  rw [coeff_iterate_derivative, show l - μ + μ = l from by omega]
  have h1 : l.descFactorial μ ≠ 0 := by
    have := Nat.descFactorial_eq_zero_iff_lt (n := l) (k := μ)
    omega
  have h2 := legendre_coeff_self_ne_zero l
  simp only [nsmul_eq_mul, ne_eq, mul_eq_zero, not_or]
  exact ⟨by exact_mod_cast h1, h2⟩

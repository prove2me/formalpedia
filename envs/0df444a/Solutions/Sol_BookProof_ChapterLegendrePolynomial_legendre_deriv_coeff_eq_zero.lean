-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:31:55.841516+00:00
-- url     : https://prove2.me/submissions/1c769e27-4ae9-415b-81be-17c17d2a117f

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.legendre_deriv_coeff_eq_zero
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_coeff_eq_zero_of_lt
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (l μ k : ℕ) (h : l < k + μ) :
    (derivative^[μ] (legendre l)).coeff k = 0 := by

  rw [coeff_iterate_derivative, legendre_coeff_eq_zero_of_lt l (k + μ) h, smul_zero]

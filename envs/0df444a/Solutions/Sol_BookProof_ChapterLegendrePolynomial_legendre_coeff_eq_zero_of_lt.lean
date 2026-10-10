-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.legendre_coeff_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:31:54.836597+00:00
-- url     : https://prove2.me/submissions/53494dbf-ee88-42e3-a995-44650ebc8071

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.legendre_coeff_eq_zero_of_lt
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_legendre_natDegree_le
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (l k : ℕ) (h : l < k) : (legendre l).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (legendre_natDegree_le l) h)

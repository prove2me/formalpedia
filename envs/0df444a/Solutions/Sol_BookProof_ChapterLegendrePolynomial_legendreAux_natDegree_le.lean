-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.legendreAux_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:31:21.873073+00:00
-- url     : https://prove2.me/submissions/41e3960d-9ee0-45c8-bdcf-29189b4606be

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.legendreAux_natDegree_le
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_natDegree_Xsq_sub_one
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) : (legendreAux l).natDegree ≤ l := by

  have h := natDegree_iterate_derivative ((X ^ 2 - 1 : ℝ[X]) ^ l) l
  have h2 : ((X ^ 2 - 1 : ℝ[X]) ^ l).natDegree = 2 * l := by
    rw [natDegree_pow, natDegree_Xsq_sub_one]; ring
  rw [legendreAux]
  omega

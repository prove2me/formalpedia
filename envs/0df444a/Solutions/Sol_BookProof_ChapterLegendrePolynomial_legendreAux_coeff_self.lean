-- Prove2me | solution 1 for BookProof.ChapterLegendrePolynomial.legendreAux_coeff_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:33:10.11334+00:00
-- url     : https://prove2.me/submissions/3c805d6d-01d8-42db-8390-845becbb6ebc

-- Generated from ChapterLegendrePolynomial.lean — solution of BookProof.ChapterLegendrePolynomial.legendreAux_coeff_self
import Mathlib
import Definitions.Def_ChapterLegendrePolynomial
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_natDegree_Xsq_sub_one
import Theorems.Thm_BookProof_ChapterLegendrePolynomial_monic_Xsq_sub_one
open BookProof.ChapterLegendrePolynomial




open Polynomial

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) :
    (legendreAux l).coeff l = ((2 * l).descFactorial l : ℝ) := by

  rw [legendreAux, coeff_iterate_derivative]
  have hm : ((X ^ 2 - 1 : ℝ[X]) ^ l).Monic := monic_Xsq_sub_one.pow l
  have hdeg : ((X ^ 2 - 1 : ℝ[X]) ^ l).natDegree = 2 * l := by
    rw [natDegree_pow, natDegree_Xsq_sub_one]; ring
  have hc : ((X ^ 2 - 1 : ℝ[X]) ^ l).coeff (l + l) = 1 := by
    have h := hm.coeff_natDegree
    rw [hdeg] at h
    rw [show l + l = 2 * l from by ring]
    exact h
  rw [hc, show l + l = 2 * l from by ring]
  simp

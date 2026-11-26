-- Prove2me | solution 1 for Eden.totalDegree_vectorFieldPolynomial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:53.885896+00:00
-- url     : https://prove2.me/submissions/cfb8ae8e-9a39-44f5-bedb-13e14e5b56f6

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
import Theorems.Thm_Eden_totalDegree_ratePolynomial_le

set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial
namespace Eden
theorem _root_.solution (c : ℝ) (i : Fin 5) :
    (vectorFieldPolynomial c i).totalDegree ≤ 5 := by
  have hr (i j k : Fin 5) : (ratePolynomial i j * X k).totalDegree ≤ 5 := by
    have h := totalDegree_mul (ratePolynomial i j) (X k)
    have h' := totalDegree_ratePolynomial_le i j
    simp only [totalDegree_X] at h
    omega
  have hl (a : ℝ) (i : Fin 5) : (C a * X i : MvPolynomial (Fin 5) ℝ).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simp)
  fin_cases i
  · exact (totalDegree_sub _ _).trans (max_le (hr 0 1 0) (by simp))
  · exact (totalDegree_add _ _).trans (max_le (hr 0 1 1) (by simp))
  · exact (totalDegree_sub _ _).trans (max_le (hr 2 3 2) ((hl _ _).trans (by omega)))
  · exact (totalDegree_add _ _).trans (max_le (hr 2 3 3) ((hl _ _).trans (by omega)))
  · exact (hl _ _).trans (by omega)
end Eden

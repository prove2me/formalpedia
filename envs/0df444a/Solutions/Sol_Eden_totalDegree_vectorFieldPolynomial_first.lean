-- Prove2me | solution 1 for Eden.totalDegree_vectorFieldPolynomial_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:42.668017+00:00
-- url     : https://prove2.me/submissions/c5510694-9fee-404a-984d-b4ae5bab9f39

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField
import Theorems.Thm_Eden_totalDegree_vectorFieldPolynomial_le
import Theorems.Thm_Eden_coeff_vectorFieldPolynomial_first

set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial
namespace Eden
theorem _root_.solution (c : ℝ) :
    (vectorFieldPolynomial c 0).totalDegree = 5 := by
  apply le_antisymm (totalDegree_vectorFieldPolynomial_le c 0)
  have h := le_totalDegree (mem_support_iff.mpr
    (show (vectorFieldPolynomial c 0).coeff (Finsupp.single 0 5) ≠ 0 by
      rw [coeff_vectorFieldPolynomial_first]; norm_num))
  simpa using h
end Eden

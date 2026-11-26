-- Prove2me | solution 1 for Eden.coeff_vectorFieldPolynomial_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:32.112626+00:00
-- url     : https://prove2.me/submissions/5aa49ea2-f370-49de-acc2-e5c82a0bef7a

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Definitions.Def_Eden_PolynomialVectorField

set_option autoImplicit true
noncomputable section
open Eden
open MvPolynomial
namespace Eden
theorem _root_.solution (c : ℝ) :
    (vectorFieldPolynomial c 0).coeff (Finsupp.single 0 5) = -1 := by
  have he : vectorFieldPolynomial c 0 =
      -(X 0 ^ 5) - C 2 * (X 0 ^ 3 * X 1 ^ 2) - X 0 * X 1 ^ 4 +
        C 3 * X 0 ^ 3 + C 3 * (X 0 * X 1 ^ 2) - C 2 * X 0 - X 1 := by
    norm_num [vectorFieldPolynomial, ratePolynomial, radiusPolynomial, map_ofNat]
    ring
  rw [he]
  simp only [coeff_sub, coeff_add, coeff_neg, coeff_C_mul]
  simp only [X_pow_eq_monomial]
  simp only [X, monomial_mul, coeff_monomial]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_succ]
end Eden

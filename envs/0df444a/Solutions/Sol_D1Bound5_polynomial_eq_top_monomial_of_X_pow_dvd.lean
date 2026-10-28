-- Prove2me | solution 1 for D1Bound5.polynomial_eq_top_monomial_of_X_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:17.722992+00:00
-- url     : https://prove2.me/submissions/2fb89735-e092-4a56-9aaa-bbe61858b354

import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Polynomial

section
open Finset Polynomial Matrix

namespace D1Bound5

/-!
This module isolates an intermediate step in the all-orders Bennett determinant
argument. It does not define the residue polynomials or prove their cancellation.
The required cancellation is an explicit hypothesis of the final theorem.
-/

section CommRing

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]





/-- A polynomial whose degree is at most `D` and whose first `D` coefficients
vanish is exactly its degree-`D` monomial, including the zero-polynomial case. -/
theorem _root_.solution (p : R[X]) (D : ℕ)
    (hdeg : p.natDegree ≤ D) (hdiv : (X : R[X]) ^ D ∣ p) :
    p = C (p.coeff D) * X ^ D := by
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  apply Polynomial.ext
  intro l
  rw [Polynomial.coeff_monomial]
  split_ifs with h
  · subst l
    rfl
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hlt)
    · exact Polynomial.X_pow_dvd_iff.mp hdiv l hgt





end CommRing

end D1Bound5
end

-- Prove2me | solution 1 for D1Bound5.polynomial_det_eq_monomial_of_residual
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:05.688754+00:00
-- url     : https://prove2.me/submissions/e200b917-0aba-4df7-91d9-674e9d586617

import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Theorems.Thm_D1Bound5_dvd_det_of_dvd_column_combination
import Theorems.Thm_D1Bound5_polynomial_det_natDegree_le_sum
import Theorems.Thm_D1Bound5_polynomial_eq_top_monomial_of_X_pow_dvd

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







/-- Intermediate all-orders determinant principle. The residual cancellation is
an explicit input. In the Bennett construction the distinguished node is zero,
so the corresponding (truncated) binomial polynomial is exactly one. -/
theorem _root_.solution (P : Matrix ι ι R[X])
    (d : ι → ℕ) (θ : ι → R[X]) (q : ι) (hθ : θ q = 1)
    (hdeg : ∀ i j, (P i j).natDegree ≤ d j)
    (hres : ∀ i, (X : R[X]) ^ (∑ j, d j) ∣ ∑ j, θ j * P i j) :
    P.det = C (P.det.coeff (∑ j, d j)) * X ^ (∑ j, d j) := by
  apply polynomial_eq_top_monomial_of_X_pow_dvd
  · exact polynomial_det_natDegree_le_sum P d hdeg
  · exact dvd_det_of_dvd_column_combination P θ q hθ _ hres



end CommRing

end D1Bound5
end

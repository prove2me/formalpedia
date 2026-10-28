-- Prove2me | solution 1 for D1Bound5.polynomial_det_natDegree_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:49.161166+00:00
-- url     : https://prove2.me/submissions/dad7b23b-2a6a-4e33-909e-be52e74e8bd9

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



/-- A columnwise degree bound gives the corresponding determinant degree bound,
without any assumption that the coefficient ring is a domain. -/
theorem _root_.solution (P : Matrix ι ι R[X]) (d : ι → ℕ)
    (hdeg : ∀ i j, (P i j).natDegree ≤ d j) :
    P.det.natDegree ≤ ∑ j, d j := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_prod_le _ _).trans
      (Finset.sum_le_sum fun i _ ↦ hdeg (σ i) i))







end CommRing

end D1Bound5
end

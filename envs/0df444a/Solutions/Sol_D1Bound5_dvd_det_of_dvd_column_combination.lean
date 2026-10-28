-- Prove2me | solution 1 for D1Bound5.dvd_det_of_dvd_column_combination
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:11:44.501828+00:00
-- url     : https://prove2.me/submissions/1787d077-08b3-4a67-bc3c-811ee24a9d2d

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

/-- Replacing a distinguished column by a linear combination of columns transfers
a common factor of the residual vector to the determinant. The coefficient of
the distinguished column is assumed to be one. -/
theorem _root_.solution (A : Matrix ι ι R) (c : ι → R)
    (q : ι) (hc : c q = 1) (z : R)
    (hres : ∀ i, z ∣ ∑ j, c j * A i j) : z ∣ A.det := by
  classical
  choose v hv using hres
  have hcol : (fun i ↦ ∑ j, c j * A i j) = z • v := by
    funext i
    exact hv i
  refine ⟨(A.updateCol q v).det, ?_⟩
  calc
    A.det = (A.updateCol q (fun i ↦ ∑ j, c j * A i j)).det := by
      symm
      simpa only [smul_eq_mul, hc, one_mul] using Matrix.det_updateCol_sum A q c
    _ = z * (A.updateCol q v).det := by
      rw [hcol, Matrix.det_updateCol_smul]









end CommRing

end D1Bound5
end

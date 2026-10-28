-- Prove2me | solution 1 for D1Bound5.normalizedRootError_det
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:32.152989+00:00
-- url     : https://prove2.me/submissions/57c5f4eb-7bb7-4971-9597-871a3d66e238

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions
import Theorems.Thm_D1Bound5_scaledRootMatrix_det

section
open scoped BigOperators
open Matrix

namespace D1Bound5













/-- Normalization (integrated-1): a scaled root matrix is a rank-one
matrix plus the correction. -/
theorem scaledRootMatrix_eq_rankOne_add_error {R n : Type*} [CommRing R]
    (a u : n → R) (M : Matrix n n R) :
    scaledRootMatrix u M =
      (fun i j => a i*a j + normalizedRootError a u M i j) := by
  ext i j
  simp [normalizedRootError]

/-- Determinant equality in (integrated-1), in any finite dimension and
without dividing by entries or square roots. -/
theorem _root_.solution {R n : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (a u : n → R) (M : Matrix n n R)
    (hu : ∀ i, (u i)^2 = a i) :
    Matrix.det (fun i j => a i*a j + normalizedRootError a u M i j) =
      (∏ i, a i) * M.det := by
  rw [← scaledRootMatrix_eq_rankOne_add_error a u M, scaledRootMatrix_det]
  have hp : (∏ i, u i)^2 = ∏ i, a i := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun i _ => hu i)
  rw [hp]



end D1Bound5
end

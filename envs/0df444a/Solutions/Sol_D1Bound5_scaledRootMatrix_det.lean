-- Prove2me | solution 1 for D1Bound5.scaledRootMatrix_det
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:34.674504+00:00
-- url     : https://prove2.me/submissions/b3a66798-80f3-41b9-ba0d-325715877438

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DeterminantNormalization_Definitions

section
open scoped BigOperators
open Matrix

namespace D1Bound5





/-- Exact determinant scaling in arbitrary finite dimension, with no
nonzero-root assumption. -/
theorem _root_.solution {R n : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] (u : n → R) (M : Matrix n n R) :
    (scaledRootMatrix u M).det = (∏ i, u i)^2 * M.det := by
  have h : scaledRootMatrix u M = Matrix.diagonal u * M * Matrix.diagonal u := by
    ext i j
    simp only [scaledRootMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring













end D1Bound5
end

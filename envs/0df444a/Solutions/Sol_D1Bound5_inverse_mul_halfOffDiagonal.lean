-- Prove2me | solution 1 for D1Bound5.inverse_mul_halfOffDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:43.998559+00:00
-- url     : https://prove2.me/submissions/90a04e05-a9f6-43ca-bd10-95c07e8f1574

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ReferenceMatrixSpectral_Definitions
import Definitions.Def_D1Bound5_RootMatrixOperatorBound_Definitions

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5





/-- The other inverse identity is also an equality over complex matrices. -/
theorem _root_.solution :
    halfOffDiagonalInverse * halfOffDiagonal = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [halfOffDiagonal, halfOffDiagonalInverse,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num












end D1Bound5
end
